#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Transforms/Utils/LoopPeel.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <map>
#include <set>
#include <unordered_set>
#include <queue>

using namespace llvm;
#define UNKNOWN nullptr
#define NO_CACHE nullptr
#define cout errs()

namespace
{
  typedef std::map<Value *, std::set<Instruction *>> RDASet;
  typedef std::map<Instruction *, RDASet> RDAMap;
  typedef std::map<Value *, std::set<Value *>> AliasSet;
  typedef std::map<Instruction *, AliasSet> AliasMap;
  typedef std::unordered_set<Value *> EscapeSet;
  typedef std::map<Instruction *, EscapeSet> EscapeMap;
  typedef std::map<Value *, Value *> CacheSet;
  typedef std::map<Instruction *, CacheSet> CacheMap;

  std::unordered_set<std::string> ignored_funcs = {"printf", "puts", "CAT_destroy", "CAT_get"};

  struct CAT : public ModulePass
  {
    static char ID;

    CAT() : ModulePass(ID) {}

    enum VType
    {
      OTHER,
      CAT_DATA,
      CAT_PTR,
    };

    // sets for RDA
    RDAMap IN, OUT;
    AliasMap aliIN, aliOUT, ptIN, ptOUT;
    EscapeMap escIN, escOUT;
    CacheMap cacheIN, cacheOUT;
    std::set<Value *> allCATData, allCATPtr;
    std::map<Instruction *, Instruction *> deleteMap;
    CallGraph *CG;

    Function *curFunc;
    Module *curModule;

    AliasAnalysis *AA;

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization(Module &M) override
    {
      curModule = &M;
      return false;
    }

    void resetGlobalMaps()
    {
      IN.clear();
      OUT.clear();
      aliIN.clear();
      aliOUT.clear();
      ptIN.clear();
      ptOUT.clear();
      escIN.clear();
      escOUT.clear();
      cacheIN.clear();
      cacheOUT.clear();
      allCATData.clear();
      allCATPtr.clear();
      deleteMap.clear();
    }

    int getSize(Value *ptr)
    {
      auto *ptrType = cast<PointerType>(ptr->getType())->getPointerElementType();
      return ptrType->isSized() ? curModule->getDataLayout().getTypeStoreSize(ptrType) : 0;
    }

    bool mayModifiedByFunc(CallInst *callInst, Value *ptr)
    {
      switch (AA->getModRefInfo(callInst, ptr, getSize(ptr)))
      {
      case ModRefInfo::Mod:
      case ModRefInfo::ModRef:
      case ModRefInfo::MustMod:
        return true;
      default:
        return false;
      }
    }

    bool mayReferencedByFunc(CallInst *callInst, Value *ptr)
    {
      switch (AA->getModRefInfo(callInst, ptr, getSize(ptr)))
      {
      case ModRefInfo::Ref:
      case ModRefInfo::ModRef:
      case ModRefInfo::MustRef:
        return true;
      default:
        return false;
      }
    }

    void mergeAliasInfo(Value *source, Value *target, AliasSet &curAliIN, AliasSet &curAliOUT)
    {
      for (auto *alias : curAliIN[source])
      {
        curAliOUT[target].insert(alias);
        curAliOUT[alias].insert(target);
      }
    }

    VType checkType(Value *v)
    {
      if (allCATData.find(v) != allCATData.end())
        return CAT_DATA;
      else if (allCATPtr.find(v) != allCATPtr.end())
        return CAT_PTR;
      else
        return OTHER;
    }

    void resetAliasInfo(Value *v, AliasSet &curAliIN, AliasSet &curAliOUT)
    {
      for (auto *alias : curAliIN[v])
        curAliOUT[alias].erase(v);
      curAliOUT[v].clear();
      curAliOUT[v].insert(v);
    }

    void addDef(Value *v, Instruction *def, AliasSet &aliases, RDASet &curOUT, CacheSet &curCacheOUT)
    {
      if (aliases.find(v) == aliases.end())
      {
        cout << "[WARNING] " << *v << " alias not init!\n";
        aliases[v].insert(v);
      }

      for (auto *alias : aliases[v])
      {
        curOUT[alias].insert(def);
        curCacheOUT[alias] = NO_CACHE;
      }
    }

    void setDef(Value *v, Instruction *def, AliasSet &aliases, RDASet &curOUT, CacheSet &curCacheOUT)
    {
      curOUT[v].clear();
      addDef(v, def, aliases, curOUT, curCacheOUT);
    }

    void addPointTo(Value *ptr, Value *val, AliasSet &aliases, AliasSet &curPtOUT)
    {
      if (aliases.find(ptr) == aliases.end())
      {
        cout << "[WARNING] " << *ptr << " alias not init!\n";
        aliases[ptr].insert(ptr);
      }

      for (auto *alias : aliases[ptr])
        curPtOUT[alias].insert(val);
    }

    void setPointTo(Value *ptr, Value *val, AliasSet &aliases, AliasSet &curPtOUT)
    {
      curPtOUT[ptr].clear();
      addPointTo(ptr, val, aliases, curPtOUT);
    }

    std::set<Value *> findAllPossibleCATData(Value *ptr, AliasSet &curPtIN)
    {
      std::set<Value *> possibleCATData;
      for (auto *pointed : curPtIN[ptr])
      {
        if (pointed == UNKNOWN)
        {
          possibleCATData.insert(UNKNOWN);
          continue;
        }

        switch (checkType(pointed))
        {
        case CAT_DATA:
          possibleCATData.insert(pointed);
          break;
        case OTHER:
          break;
        case CAT_PTR:
          auto rst = findAllPossibleCATData(pointed, curPtIN);
          possibleCATData.insert(rst.begin(), rst.end());
          break;
        }
      }

      return possibleCATData;
    }

    void collectTypeInfo()
    {
      while (true)
      {
        bool fixed = false;
        for (auto &B : *curFunc)
          fixed |= collectTypeInfoInBB(B);
        if (!fixed)
          break;
      }

      // sweep the type info in the whole function
      sweepTypeInfoInBB();
    }

    void sortAccordingToType(Value *v)
    {
      if (!v->getType()->isPointerTy() || checkType(v) != OTHER)
        return;
      auto *ptrType = cast<PointerType>(v->getType());
      if (ptrType->getPointerElementType()->isIntegerTy(8))
        allCATData.insert(v);
      else
        allCATPtr.insert(v);
    }

    void sweepTypeInfoInBB()
    {
      // sweep globals
      for (auto &GV : curModule->globals())
        if (auto *ptrType = dyn_cast<PointerType>(GV.getType()))
        {
          if (checkType(&GV) != OTHER)
            continue;
          if (ptrType->getPointerElementType()->isIntegerTy(8))
            allCATData.insert(&GV);
          else
            allCATPtr.insert(&GV);
        }

      for (auto &BB : *curFunc)
        for (auto &I : BB)
        {
          if (auto *allocaInst = dyn_cast<AllocaInst>(&I))
            sortAccordingToType(allocaInst);
          else if (auto *phiNode = dyn_cast<PHINode>(&I))
            sortAccordingToType(phiNode);
          else if (auto *selectInst = dyn_cast<SelectInst>(&I))
            sortAccordingToType(selectInst);
          else if (auto *storeInst = dyn_cast<StoreInst>(&I))
          {
            sortAccordingToType(storeInst->getPointerOperand());
            sortAccordingToType(storeInst->getValueOperand());
          }
          else if (auto *loadInst = dyn_cast<LoadInst>(&I))
          {
            sortAccordingToType(loadInst->getPointerOperand());
            sortAccordingToType(loadInst);
          }
          else if (auto *bitcastInst = dyn_cast<BitCastInst>(&I))
          {
            sortAccordingToType(bitcastInst);
            sortAccordingToType(bitcastInst->getOperand(0));
          }
          else if (auto *callInst = dyn_cast<CallInst>(&I))
            sortAccordingToType(callInst);
        }
    }

    bool collectTypeInfoInBB(BasicBlock &BB)
    {
      auto oldDataSize = allCATData.size(), oldPtrSize = allCATPtr.size();
      for (auto &I : BB)
      {
        if (auto *allocaInst = dyn_cast<AllocaInst>(&I))
          allCATPtr.insert(allocaInst);
        else if (auto *phiNode = dyn_cast<PHINode>(&I))
        {
          int n = phiNode->getNumIncomingValues();
          switch (checkType(phiNode))
          {
          case CAT_DATA:
            for (int i = 0; i < n; i++)
              allCATData.insert(phiNode->getIncomingValue(i));
            break;
          case CAT_PTR:
            for (int i = 0; i < n; i++)
              allCATPtr.insert(phiNode->getIncomingValue(i));
            break;
          case OTHER:
            for (int i = 0; i < n; i++)
            {
              switch (checkType(phiNode->getIncomingValue(i)))
              {
              case CAT_DATA:
                allCATData.insert(phiNode);
                break;
              case CAT_PTR:
                allCATPtr.insert(phiNode);
                break;
              case OTHER:
                break;
              }
            }
            break;
          }
        }
        else if (auto *selectInst = dyn_cast<SelectInst>(&I))
        {
          auto *op1 = selectInst->getOperand(1), *op2 = selectInst->getOperand(2);
          switch (checkType(selectInst))
          {
          case CAT_DATA:
            allCATData.insert(op1);
            allCATData.insert(op2);
            break;
          case CAT_PTR:
            allCATPtr.insert(op1);
            allCATPtr.insert(op2);
            break;
          case OTHER:
            // if can't find type, then check the type of operands
            for (auto *op : {op1, op2})
              switch (checkType(op))
              {
              case CAT_DATA:
                allCATData.insert(op);
                break;
              case CAT_PTR:
                allCATPtr.insert(op);
                break;
              case OTHER:
                break;
              }
            break;
          }
        }
        else if (auto *storeInst = dyn_cast<StoreInst>(&I))
          switch (checkType(storeInst->getValueOperand()))
          {
          case CAT_DATA:
          case CAT_PTR:
            allCATPtr.insert(storeInst->getPointerOperand());
            break;
          case OTHER:
            break;
          }
        else if (auto *loadInst = dyn_cast<LoadInst>(&I))
        {
          switch (checkType(loadInst))
          {
          case CAT_DATA:
          case CAT_PTR:
            allCATPtr.insert(loadInst->getPointerOperand());
            break;
          case OTHER:
            break;
          }
        }
        else if (auto *callInst = dyn_cast<CallInst>(&I))
        {
          auto calledName = callInst->getCalledFunction()->getName();
          if (calledName.equals("CAT_new"))
            allCATData.insert(callInst);
          else if (calledName.equals("CAT_get") || calledName.equals("CAT_set") || calledName.equals("CAT_destroy"))
            allCATData.insert(callInst->getArgOperand(0));
          else if (calledName.equals("CAT_add") || calledName.equals("CAT_sub"))
            for (int i = 0; i < 3; i++)
              allCATData.insert(callInst->getArgOperand(i));
        }
      }
      return allCATData.size() != oldDataSize || allCATPtr.size() != oldPtrSize;
    }

    bool RDAinBB(BasicBlock &BB)
    {
      RDASet curIN, curOUT;
      AliasSet curAliIN, curAliOUT, curPtIN, curPtOUT;
      EscapeSet curEscIN, curEscOUT;
      CacheSet curCacheIN, curCacheOUT;
      // create two temporary sets for comparing old OUT and new OUT
      std::unordered_set<Instruction *> oldOut, newOut;
      bool firstTime = true;

      firstTime = OUT.find(BB.getTerminator()) == OUT.end();

      for (auto &pair : OUT[BB.getTerminator()])
        for (auto *I : pair.second)
          oldOut.insert(I);

      // merge the predecessors' information
      if (!predecessors(&BB).empty())
        for (auto *PB : predecessors(&BB))
        {
          for (auto &pair : OUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curIN[pair.first].insert(I);

          for (auto &pair : aliOUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curAliIN[pair.first].insert(I);

          for (auto &pair : ptOUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curPtIN[pair.first].insert(I);

          // merge the escape information
          auto &predEscOUT = escOUT[PB->getTerminator()];
          curEscIN.insert(predEscOUT.begin(), predEscOUT.end());
        }
      else
      {
        // if the block has no predecessors, then it's the entry block
        // entry block will only be entered once at the beginning of the analysis
        // initialize the RDA for arguments and globals
        for (auto &arg : BB.getParent()->args())
          switch (checkType(&arg))
          {
          case CAT_DATA:
            curIN[&arg].insert(UNKNOWN);
            break;
          case CAT_PTR:
            curPtIN[&arg].insert(UNKNOWN);
            break;
          case OTHER:
            break;
          }

        for (auto &GV : curModule->globals())
          switch (checkType(&GV))
          {
          case CAT_DATA:
            curIN[&GV].insert(UNKNOWN);
            break;
          case CAT_PTR:
            curPtIN[&GV].insert(UNKNOWN);
            break;
          case OTHER:
            break;
          }

        // initialize the alias information
        for (Value *v : allCATData)
          curAliIN[v].insert(v);
        for (Value *v : allCATPtr)
          curAliIN[v].insert(v);
      }

      // calculate IN and OUT for each instruction in the current block
      for (auto &I : BB)
      {
        IN[&I] = curIN;
        curOUT = curIN;
        aliIN[&I] = curAliIN;
        curAliOUT = curAliIN;
        ptIN[&I] = curPtIN;
        curPtOUT = curPtIN;
        escIN[&I] = curEscIN;
        curEscOUT = curEscIN;
        cacheIN[&I] = curCacheIN;
        curCacheOUT = curCacheIN;

        // PHI
        if (I.getType()->isPointerTy() && isa<PHINode>(I))
        {
          // aliasing/multiple definition may be happening
          // for now we only consider the case where the definition is a pointer (CAT are all pointers)
          auto *phiNode = cast<PHINode>(&I);
          // reset its alias info
          resetAliasInfo(phiNode, curAliIN, curAliOUT);
          // merge alias info
          int n = phiNode->getNumIncomingValues();
          for (int i = 0; i < n; i++)
          {
            auto *predBB = phiNode->getIncomingBlock(i);
            auto *incomingVal = phiNode->getIncomingValue(i);
            // merge the aliasing information
            for (auto *alias : aliOUT[predBB->getTerminator()][incomingVal])
            {
              curAliOUT[phiNode].insert(alias);
              curAliOUT[alias].insert(phiNode);
            }
          }

          switch (checkType(phiNode))
          {
          case CAT_DATA:
            // clear the RDA set
            curOUT[phiNode].clear();
            // merge RDA info
            for (int i = 0; i < n; i++)
            {
              auto *predBB = phiNode->getIncomingBlock(i);
              auto *incomingVal = phiNode->getIncomingValue(i);
              auto predRDA = OUT[predBB->getTerminator()][incomingVal];
              curOUT[phiNode].insert(predRDA.begin(), predRDA.end());
            }
            break;
          case CAT_PTR:
            // clear the point-to set
            curPtOUT[phiNode].clear();
            // merge point-to info
            for (int i = 0; i < n; i++)
            {
              auto *predBB = phiNode->getIncomingBlock(i);
              auto *incomingVal = phiNode->getIncomingValue(i);
              auto predPt = ptOUT[predBB->getTerminator()][incomingVal];
              curPtOUT[phiNode].insert(predPt.begin(), predPt.end());
            }
            break;
          case OTHER:
            break;
          }
        }
        // SELECT
        else if (I.getType()->isPointerTy() && isa<SelectInst>(I))
        {
          auto *selectInst = cast<SelectInst>(&I);
          auto *op1 = selectInst->getOperand(1), *op2 = selectInst->getOperand(2);

          resetAliasInfo(selectInst, curAliIN, curAliOUT);
          for (auto *op : {op1, op2})
            for (auto *alias : curAliIN[op])
            {
              curAliOUT[selectInst].insert(alias);
              curAliOUT[alias].insert(selectInst);
            }

          switch (checkType(selectInst))
          {
          case CAT_DATA:
            curOUT[selectInst].clear();
            for (auto *op : {op1, op2})
              curOUT[selectInst].insert(curIN[op].begin(), curIN[op].end());
            break;
          case CAT_PTR:
            curPtOUT[selectInst].clear();
            for (auto *op : {op1, op2})
              curPtOUT[selectInst].insert(curPtIN[op].begin(), curPtIN[op].end());
            break;
          case OTHER:
            break;
          }
        }
        // ALLOCA
        else if (auto *allocaInst = dyn_cast<AllocaInst>(&I))
        {
          if (checkType(allocaInst) == CAT_PTR)
          {
            resetAliasInfo(allocaInst, curAliIN, curAliOUT);
            curPtOUT[allocaInst].clear();
          }
          else
            cout << "[WARNING] In " << *allocaInst << " the ptr is not recognized\n";
        }
        // STORE
        else if (auto *storeInst = dyn_cast<StoreInst>(&I))
        {
          auto *ptr = storeInst->getPointerOperand();
          auto *value = storeInst->getValueOperand();
          if (checkType(ptr) == CAT_PTR)
            setPointTo(ptr, value, curAliIN, curPtOUT);
          else
            cout << "[WARNING] In " << *storeInst << " the ptr is not recognized\n";
        }
        // LOAD
        else if (auto *loadInst = dyn_cast<LoadInst>(&I))
        {
          auto *ptr = loadInst->getPointerOperand();

          if (checkType(ptr) == CAT_PTR)
          {
            // reset for loaded value
            resetAliasInfo(loadInst, curAliIN, curAliOUT);
            for (auto *pointed : curPtIN[ptr])
            {
              if (pointed == UNKNOWN)
                continue;
              for (auto *alias : curAliIN[pointed])
              {
                curAliOUT[loadInst].insert(alias);
                curAliOUT[alias].insert(loadInst);
              }
            }

            switch (checkType(loadInst))
            {
            case CAT_DATA:
              curOUT[loadInst].clear();
              for (auto *pointed : curPtIN[ptr])
                if (pointed == UNKNOWN)
                  curOUT[loadInst].insert(UNKNOWN);
                else if (checkType(pointed) != CAT_DATA)
                  cout << "[WARNING] In " << *loadInst << " trying to assign invalid type to DATA\n";
                else
                  curOUT[loadInst].insert(curIN[pointed].begin(), curIN[pointed].end());
              break;
            case CAT_PTR:
              curPtOUT[loadInst].clear();
              for (auto *pointed : curPtIN[ptr])
                if (pointed == UNKNOWN)
                  curPtOUT[loadInst].insert(UNKNOWN);
                else if (checkType(pointed) != CAT_PTR)
                  cout << "[WARNING] In " << *loadInst << " trying to assign invalid type to PTR\n";
                else
                  curPtOUT[loadInst].insert(curPtIN[pointed].begin(), curPtIN[pointed].end());
              break;
            case OTHER:
              break;
            }
            // if previously there is only UNKNOWN in curPtIN, then delegate the UNKNOWN to loaded value
            curPtOUT[ptr].erase(UNKNOWN);
            // add a new relationship
            addPointTo(ptr, loadInst, curAliIN, curPtOUT);
          }
          else
            cout << "[WARNING] In " << *loadInst << " the ptr is not recognized\n";
        }
        // BITCAST: add alias info
        else if (auto *bitcastInst = dyn_cast<BitCastInst>(&I))
        {
          auto *casted = bitcastInst->getOperand(0);
          resetAliasInfo(bitcastInst, curAliIN, curAliOUT);
          for (auto *alias : curAliIN[casted])
          {
            curAliOUT[bitcastInst].insert(alias);
            curAliOUT[alias].insert(bitcastInst);
          }
          switch (checkType(bitcastInst))
          {
          case CAT_DATA:
            curOUT[bitcastInst].clear();
            curOUT[bitcastInst].insert(curIN[casted].begin(), curIN[casted].end());
            break;
          case CAT_PTR:
            curPtOUT[bitcastInst].clear();
            curPtOUT[bitcastInst].insert(curPtIN[casted].begin(), curPtIN[casted].end());
            break;
          case OTHER:
            break;
          }
        }
        // CAT OP: changes RDA of the first operand
        else if (auto *callInst = dyn_cast<CallInst>(&I))
        {
          auto calledName = callInst->getCalledFunction()->getName();
          if (calledName.equals("CAT_new"))
          {
            // reset the aliasing information
            resetAliasInfo(callInst, curAliIN, curAliOUT);
            setDef(callInst, callInst, curAliOUT, curOUT, curCacheOUT);
          }
          else if (calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set"))
          {
            Value *gen = callInst->getArgOperand(0);
            setDef(gen, callInst, curAliOUT, curOUT, curCacheOUT);
          }
          // MISC FUNC
          else if (ignored_funcs.find(calledName.str()) == ignored_funcs.end() && !calledName.startswith("llvm.lifetime"))
          {
            std::set<Value *> possibleDataPassedIn, possiblePtrPassedIn, possiblePtrModified;

            // add globals
            for (auto &GV : curModule->globals())
              switch (checkType(&GV))
              {
              case CAT_DATA:
                possibleDataPassedIn.insert(&GV);
                break;
              case OTHER:
                break;
              case CAT_PTR:
                possiblePtrPassedIn.insert(&GV);
                if (mayReferencedByFunc(callInst, &GV))
                {
                  auto possibleCATData = findAllPossibleCATData(&GV, curPtIN);
                  possibleDataPassedIn.insert(possibleCATData.begin(), possibleCATData.end());
                }
                break;
              }

            for (unsigned i = 0; i < callInst->getNumOperands() - 1; i++)
            {
              auto *arg = callInst->getArgOperand(i);
              switch (checkType(arg))
              {
              case CAT_DATA:
                possibleDataPassedIn.insert(arg);
                break;
              case OTHER:
                break;
              case CAT_PTR:
                possiblePtrPassedIn.insert(arg);
                if (mayReferencedByFunc(callInst, arg))
                {
                  auto possibleCATData = findAllPossibleCATData(arg, curPtIN);
                  possibleDataPassedIn.insert(possibleCATData.begin(), possibleCATData.end());
                }
                break;
              }
            }

            for (auto *ptr : possiblePtrPassedIn)
              if (mayModifiedByFunc(callInst, ptr))
                possiblePtrModified.insert(ptr);

            for (auto *data : possibleDataPassedIn)
              if (data == UNKNOWN)
                continue;
              else if (mayModifiedByFunc(callInst, data))
                setDef(data, UNKNOWN, curAliIN, curOUT, curCacheOUT);

            // modified PTR can point to any passed in DATA
            for (auto *ptr : possiblePtrModified)
              for (auto *data : possibleDataPassedIn)
                addPointTo(ptr, data, curAliIN, curPtOUT);

            // the return value can be alias of any same-level argument
            switch (checkType(callInst))
            {
            case CAT_DATA:
              // merge all info of possible CAT_data
              resetAliasInfo(callInst, curAliIN, curAliOUT);
              curOUT[callInst].clear();

              // it could be pointed by any possible CAT_ptr modified
              for (auto *ptr : possiblePtrModified)
                curPtOUT[ptr].insert(callInst);

              for (auto *data : possibleDataPassedIn)
              {
                if (data == UNKNOWN)
                  curOUT[callInst].insert(UNKNOWN);
                else if (AA->alias(data, getSize(data), callInst, getSize(callInst)) == AliasResult::NoAlias)
                  continue;
                else
                {
                  curOUT[callInst].insert(curOUT[data].begin(), curOUT[data].end());
                  mergeAliasInfo(data, callInst, curAliIN, curAliOUT);
                }
              }
              break;
            case CAT_PTR:
              // merge all info of possible CAT_ptr
              resetAliasInfo(callInst, curAliIN, curAliOUT);
              curPtOUT[callInst].clear();
              for (auto *ptr : possiblePtrPassedIn)
              {
                if (AA->alias(ptr, getSize(ptr), callInst, getSize(callInst)) == AliasResult::NoAlias)
                  continue;
                curPtOUT[callInst].insert(curPtOUT[ptr].begin(), curPtOUT[ptr].end());
                mergeAliasInfo(ptr, callInst, curAliIN, curAliOUT);
              }
              break;
            case OTHER:
              break;
            }
          }
        }

        OUT[&I] = curOUT;
        curIN = curOUT;
        aliOUT[&I] = curAliOUT;
        curAliIN = curAliOUT;
        ptOUT[&I] = curPtOUT;
        curPtIN = curPtOUT;
        escOUT[&I] = curEscOUT;
        curEscIN = curEscOUT;
        cacheOUT[&I] = curCacheOUT;
        curCacheIN = curCacheOUT;
      }

      // if the block is analyzed for the first time, then we need to add its successors to the queue
      if (firstTime)
        return true;

      // the block is analyzed before, so we need to compare the old OUT with the new OUT
      for (auto &pair : OUT[BB.getTerminator()])
        for (auto *I : pair.second)
          newOut.insert(I);

      if (oldOut.size() != newOut.size())
        return true;

      for (auto *I : oldOut)
        // found a difference, so the block is changed
        if (newOut.find(I) == newOut.end())
          return true;

      // the block is not changed if the two sets are equal
      return false;
    }

    void dumpRDAInfo()
    {
      cout << "Function \"" << curFunc->getName() << "\"\n";

      for (auto &BB : *curFunc)
        for (auto &I : BB)
        {
          cout << "INSTRUCTION: " << I << "\n***************** RDA IN\n{\n";
          for (auto &pair : IN[&I])
          {
            cout << "DEF OF " << *pair.first << ":\n";
            for (auto *def : pair.second)
              if (def)
                cout << "  " << *def << "\n";
              else
                cout << "  UNKNOWN\n";
          }
          cout << "}\n**************************************\n";

          cout << "***************** POINT-TO IN\n{\n";
          for (auto &pair : ptIN[&I])
          {
            cout << "DEF OF " << *pair.first << ":\n";
            for (auto *def : pair.second)
              if (def)
                cout << "  " << *def << "\n";
              else
                cout << "  UNKNOWN\n";
          }
          cout << "}\n**************************************\n";

          cout << "***************** RDA OUT\n{\n";
          for (auto &pair : OUT[&I])
          {
            cout << "DEF OF " << *pair.first << ":\n";
            for (auto *def : pair.second)
              if (def)
                cout << "  " << *def << "\n";
              else
                cout << "  UNKNOWN\n";
          }
          cout << "}\n**************************************\n";

          cout << "***************** POINT-TO OUT\n{\n";
          for (auto &pair : ptOUT[&I])
          {
            cout << "DEF OF " << *pair.first << ":\n";
            for (auto *def : pair.second)
              if (def)
                cout << "  " << *def << "\n";
              else
                cout << "  UNKNOWN\n";
          }
          cout << "}\n**************************************\n";
        }
    }

    void dumpTypeInfo()
    {
      cout << "Function \"" << curFunc->getName() << "\"\n";
      cout << "CAT data:\n";
      for (auto *v : allCATData)
        cout << "  " << *v << "\n";
      cout << "CAT pointers:\n";
      for (auto *v : allCATPtr)
        cout << "  " << *v << "\n";
    }

    ConstantInt *getIfIsConstant(Value *operand, RDASet &curIN)
    {
      ConstantInt *constant = nullptr;

      for (auto *def : curIN[operand])
      {
        // def may be UNKNOWN, which means the operand may be defined outside the function
        if (def == UNKNOWN)
          return nullptr;

        if (deleteMap.find(def) != deleteMap.end())
          def = deleteMap[def];

        Value *candidate = nullptr;
        if (auto *callInst = dyn_cast<CallInst>(def))
        {
          auto calledName = callInst->getCalledFunction()->getName();
          if (calledName.equals("CAT_new"))
            candidate = callInst->getOperand(0);
          else if (calledName.equals("CAT_set"))
            candidate = callInst->getOperand(1);
          else
            // CAT_add, CAT_sub, or passed into functions
            candidate = nullptr;
        }

        if (!candidate || !isa<ConstantInt>(candidate))
          return nullptr;

        if (!constant)
          constant = cast<ConstantInt>(candidate);
        else if (constant->getValue() != cast<ConstantInt>(candidate)->getValue())
          return nullptr;
      }

      return constant;
    }

    bool constantFoldAndAlgSimp()
    {
      if (!curModule->getFunction("CAT_set"))
        return false;

      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      for (auto &B : curFunc->getBasicBlockList())
        for (auto &I : B)
          instructions.push_back(&I);

      for (auto *I : instructions)
      {
        if (!isa<CallInst>(I))
          continue;

        auto *callInst = cast<CallInst>(I);
        auto calledName = callInst->getCalledFunction()->getName();

        if (!(calledName.equals("CAT_add") || calledName.equals("CAT_sub")))
          continue;

        IRBuilder<> builder(callInst);
        Value *newOperand;

        // check if all the definitions of the operands that reach the call instruction are constant
        auto op1 = callInst->getOperand(1);
        auto op2 = callInst->getOperand(2);

        // algebraic simplification of sub: x - x = 0
        if (calledName.equals("CAT_sub") && op1 == op2)
        {
          newOperand = ConstantInt::get(Type::getInt64Ty(curFunc->getContext()), 0);
          deleteMap[callInst] = builder.CreateCall(curModule->getFunction("CAT_set"), std::vector<Value *>({callInst->getOperand(0), newOperand}));
          deleteList.push_back(callInst);
          continue;
        }

        // check the constantness of the operands
        auto *constant1 = getIfIsConstant(op1, IN[I]), *constant2 = getIfIsConstant(op2, IN[I]);
        if (!constant1 && !constant2)
          continue;

        // if both operands are constant, constant fold
        if (constant1 && constant2)
          newOperand = calledName.equals("CAT_add") ? builder.CreateAdd(constant1, constant2) : builder.CreateSub(constant1, constant2);
        // if one of the operands is constant 0, then we can do the algebraic simplification
        else if (!constant1 && isa<ConstantInt>(constant2) && cast<ConstantInt>(constant2)->getValue() == 0)
          newOperand = builder.CreateCall(curModule->getFunction("CAT_get"), std::vector<Value *>({op1}));
        else if (!constant2 && isa<ConstantInt>(constant1) && cast<ConstantInt>(constant1)->getValue() == 0 && calledName.equals("CAT_add"))
          // if the operation is CAT_sub and the second operand is not constant, then we can't simplify it because we need to do negation
          newOperand = builder.CreateCall(curModule->getFunction("CAT_get"), std::vector<Value *>({op2}));
        else
          continue;

        deleteMap[callInst] = builder.CreateCall(curModule->getFunction("CAT_set"), std::vector<Value *>({callInst->getOperand(0), newOperand}));
        deleteList.push_back(callInst);
      }
      for (auto *I : deleteList)
        I->eraseFromParent();

      return deleteList.size() > 0;
    }

    bool constantProp()
    {
      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      for (auto &B : curFunc->getBasicBlockList())
        for (auto &I : B)
          instructions.push_back(&I);

      for (auto *I : instructions)
      {
        if (!isa<CallInst>(I))
          continue;
        auto *callInst = cast<CallInst>(I);
        auto calledName = callInst->getCalledFunction()->getName();

        if (!calledName.equals("CAT_get"))
          continue;

        auto *constant = getIfIsConstant(callInst->getOperand(0), IN[I]);
        if (!constant)
          continue;

        callInst->replaceAllUsesWith(constant);
        deleteList.push_back(callInst);
      }

      for (auto I : deleteList)
        I->eraseFromParent();

      return deleteList.size() > 0;
    }

    void RDA()
    {
      std::queue<BasicBlock *> toBeAnalyzed;

      // initialize the queue with all the blocks without predecessors
      for (auto &B : *curFunc)
        if (predecessors(&B).empty())
          toBeAnalyzed.push(&B);

      while (!toBeAnalyzed.empty())
      {
        auto *BB = toBeAnalyzed.front();
        toBeAnalyzed.pop();

        // try to analyze the block
        // if the block is changed, add its successors to the queue
        if (RDAinBB(*BB))
          for (auto *suc : successors(BB))
            toBeAnalyzed.push(suc);
      }
    }

    bool transformLoops()
    {
      bool changed = false;
      auto &LI = getAnalysis<LoopInfoWrapperPass>(*curFunc).getLoopInfo();
      auto &DT = getAnalysis<DominatorTreeWrapperPass>(*curFunc).getDomTree();
      auto &SE = getAnalysis<ScalarEvolutionWrapperPass>(*curFunc).getSE();
      auto &AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(*curFunc);
      const auto &TTI = getAnalysis<TargetTransformInfoWrapperPass>().getTTI(*curFunc);
      OptimizationRemarkEmitter ORE(curFunc);

      for (auto *L : LI)
      {
        auto loop = &*L;
        changed |= walkLoop(LI, loop, DT, SE, AC, ORE, TTI);
      }
      return changed;
    }

    bool walkLoop(
        LoopInfo &LI,
        Loop *loop,
        DominatorTree &DT,
        ScalarEvolution &SE,
        AssumptionCache &AC,
        OptimizationRemarkEmitter &ORE,
        const TargetTransformInfo &TTI)
    {
      cout << loop << "\n";
      if (loop->isLoopSimplifyForm() && loop->isLCSSAForm(DT))
      {
        auto tripCount = SE.getSmallConstantTripCount(loop);
        if (tripCount > 0)
        {
          UnrollLoopOptions ULO;
          ULO.Count = tripCount;
          ULO.Force = false;
          ULO.Runtime = false;
          ULO.AllowExpensiveTripCount = true;
          ULO.UnrollRemainder = false;
          ULO.ForgetAllSCEV = true;
          auto unrolled = UnrollLoop(loop, ULO, &LI, &SE, &DT, &AC, &TTI, &ORE, true);
          if (unrolled != LoopUnrollResult::Unmodified)
            return true;
        }
      }

      auto subLoops = loop->getSubLoops();
      for (auto j : subLoops)
      {
        auto subloop = &*j;
        if (walkLoop(LI, subloop, DT, SE, AC, ORE, TTI))
          return true;
      }

      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction(Function &F)
    {
      bool changed = false;
      bool unrolled = false;
      resetGlobalMaps();
      curFunc = &F;

      AA = &getAnalysis<AAResultsWrapperPass>(F).getAAResults();
      collectTypeInfo();
      RDA();
      // dumpTypeInfo();
      // dumpRDAInfo();

      changed |= constantFoldAndAlgSimp();
      changed |= constantProp();

      changed |= transformLoops();

      return changed;
    }

    bool runOnModule(Module &M) override
    {

      this->CG = &(getAnalysis<CallGraphWrapperPass>().getCallGraph());
      bool modified = false;

      for (auto &F : M)
        if (!F.isDeclaration())
        {
          if (F.hasFnAttribute(llvm::Attribute::NoInline))
            F.removeFnAttr(llvm::Attribute::NoInline);
          F.addFnAttr(llvm::Attribute::AlwaysInline);
          modified = true;
        }

      for (auto &F : M)
      {
        if (F.isDeclaration())
          continue;
        modified |= runOnFunction(F);
      }

      return modified;
    }
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override
    {

      AU.addRequired<CallGraphWrapperPass>();
      AU.addRequired<AAResultsWrapperPass>();
      AU.addRequired<AssumptionCacheTracker>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<ScalarEvolutionWrapperPass>();
      AU.addRequired<TargetTransformInfoWrapperPass>();
      // nothing is preserved, so we don't need to do anything here
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT *_PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
                                        [](const PassManagerBuilder &, legacy::PassManagerBase &PM)
                                        {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());} }); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
                                        [](const PassManagerBuilder &, legacy::PassManagerBase &PM)
                                        {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); } }); // ** for -O0
