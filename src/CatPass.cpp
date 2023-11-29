#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include <map>
#include <set>
#include <unordered_set>
#include <queue>

using namespace llvm;
#define PASSED_IN nullptr
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
  typedef std::map<Instruction *, bool> DCEMap;

  struct CAT : public FunctionPass
  {
    static char ID;

    CAT() : FunctionPass(ID) {}

    // sets for RDA
    RDAMap IN, OUT;
    AliasMap aliIN, aliOUT;
    EscapeMap escIN, escOUT;

    Function *curFunc;
    Module *curModule;

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization(Module &M) override
    {
      curModule = &M;
      return false;
    }

    void resetAliasInfo(Value *v, AliasSet &curAliIN, AliasSet &curAliOUT)
    {
      for (auto *alias : curAliIN[v])
        curAliOUT[alias].erase(v);
      curAliOUT[v].clear();
      curAliOUT[v].insert(v);
    }

    void addDef(Value *v, Instruction *def, AliasSet &aliases, RDASet &curOUT)
    {
      curOUT[v].clear();
      for (auto *alias : aliases[v])
        curOUT[alias].insert(def);
    }

    bool RDAinBB(BasicBlock &BB)
    {
      RDASet curIN, curOUT;
      AliasSet curAliIN, curAliOUT;
      EscapeSet curEscIN, curEscOUT;
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
          // merge the reaching definitions
          for (auto &pair : OUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curIN[pair.first].insert(I);

          // merge the aliasing information
          for (auto &pair : aliOUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curAliIN[pair.first].insert(I);

          // merge the store information
          auto &predStOUT = escOUT[PB->getTerminator()];
          curEscIN.insert(predStOUT.begin(), predStOUT.end());
        }
      else
        // if the block has no predecessors, then it's the entry block
        // initialize the IN of the entry block to the arguments
        for (auto &arg : BB.getParent()->args())
        {
          curIN[&arg].clear();
          curIN[&arg].insert(PASSED_IN);
          curAliIN[&arg].clear();
          curAliIN[&arg].insert(&arg);
        }

      // calculate IN and OUT for each instruction in the current block
      for (auto &I : BB)
      {
        IN[&I] = curIN;
        curOUT = curIN;
        aliIN[&I] = curAliIN;
        curAliOUT = curAliIN;
        escIN[&I] = curEscIN;
        curEscOUT = curEscIN;

        // PHI
        if (I.getType()->isPointerTy() && isa<PHINode>(I))
        {
          // aliasing/multiple definition may be happening
          // for now we only consider the case where the definition is a pointer (CAT are all pointers)
          auto *phiNode = cast<PHINode>(&I);

          // reset its alias info
          resetAliasInfo(phiNode, curAliIN, curAliOUT);
          // clear the RDA set
          curOUT[phiNode].clear();

          // for each incoming value, add the aliasing information and merge their reaching definitions
          // only consider the information in the corresponding predecessor
          Value *incomingVal;
          BasicBlock *predBB;
          int n = phiNode->getNumIncomingValues();
          for (int i = 0; i < n; i++)
          {
            incomingVal = phiNode->getIncomingValue(i);
            predBB = phiNode->getIncomingBlock(i);
            // if the predecessor is not analyzed yet, skip
            if (OUT.find(predBB->getTerminator()) == OUT.end())
              continue;

            // merge the reaching definitions
            // reaching defs of the incoming value
            std::set<Instruction *> reachingDefs = OUT[predBB->getTerminator()][incomingVal];
            curOUT[phiNode].insert(reachingDefs.begin(), reachingDefs.end());

            // merge the aliasing information
            for (auto *alias : aliOUT[predBB->getTerminator()][incomingVal])
            {
              curAliOUT[phiNode].insert(alias);
              curAliOUT[alias].insert(phiNode);
            }
          }
        }
        // SELECT
        else if (I.getType()->isPointerTy() && isa<SelectInst>(I))
        {
          auto *selectInst = cast<SelectInst>(&I);
          auto *op1 = selectInst->getOperand(1), *op2 = selectInst->getOperand(2);

          resetAliasInfo(selectInst, curAliIN, curAliOUT);
          curOUT[selectInst].clear();

          for (auto *op : {op1, op2})
          {
            for (auto *alias : curAliIN[op])
            {
              curAliOUT[selectInst].insert(alias);
              curAliOUT[alias].insert(selectInst);
            }
            curOUT[selectInst].insert(curIN[op].begin(), curIN[op].end());
          }
        }
        // STORE
        else if (auto *storeInst = dyn_cast<StoreInst>(&I))
        {
          auto *val = storeInst->getValueOperand();
          // put the saved value into escape set
          curEscOUT.insert(val);
        }
        // LOAD
        else if (I.getType()->isPointerTy() && isa<LoadInst>(&I))
        {
          auto *loadInst = cast<LoadInst>(&I);
          // all the variables in escape set may be alias of this load instruction
          // clear RDA info and aliasing information
          resetAliasInfo(loadInst, curAliIN, curAliOUT);
          curOUT[loadInst].clear();
          // merge RDA info and aliasing information
          for (auto *v : curEscIN)
          {
            for (auto *alias : curAliIN[v])
            {
              curAliOUT[loadInst].insert(alias);
              curAliOUT[alias].insert(loadInst);
            }
            curOUT[loadInst].insert(curIN[v].begin(), curIN[v].end());
          }
          // the loaded value is also escaped
          curEscOUT.insert(loadInst);
        }
        // assignment to CAT_data
        else if (auto *callInst = dyn_cast<CallInst>(&I))
        {
          Value *gen = nullptr;
          auto calledName = callInst->getCalledFunction()->getName();
          if (calledName.equals("CAT_new"))
          {
            gen = callInst;
            // reset the aliasing information
            resetAliasInfo(gen, curAliIN, curAliOUT);
            addDef(gen, callInst, curAliOUT, curOUT);
          }
          else if (calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set"))
          {
            gen = callInst->getArgOperand(0);
            addDef(gen, callInst, curAliOUT, curOUT);
          }
          else if (!calledName.equals("CAT_get") && !calledName.equals("CAT_destroy") && !calledName.equals("printf") && !calledName.startswith("llvm.lifetime"))
          {
            // dealing with references that are passed into functions
            for (unsigned i = 0; i < callInst->getNumOperands() - 1; i++)
            {
              auto *arg = callInst->getArgOperand(i);
              if (!arg->getType()->isPointerTy())
                continue;

              if (curIN.find(arg) != curIN.end())
              {
                // escape the value
                curEscOUT.insert(arg);
                addDef(arg, callInst, curAliIN, curOUT);
              }
            }

            for (auto *v : curEscIN)
              addDef(v, callInst, curAliIN, curOUT);

            // if the function returns a pointer, then we consider it as the alias of all escaped values
            // it may also be escaped
            if (callInst->getType()->isPointerTy())
            {
              gen = callInst;
              resetAliasInfo(gen, curAliIN, curAliOUT);
              for (auto *v : curEscIN)
              {
                curAliOUT[gen].insert(v);
                curAliOUT[v].insert(gen);
              }
              curEscOUT.insert(gen);
              addDef(gen, callInst, curAliOUT, curOUT);
            }
          }
        }

        OUT[&I] = curOUT;
        curIN = curOUT;
        aliOUT[&I] = curAliOUT;
        curAliIN = curAliOUT;
        escOUT[&I] = curEscOUT;
        curEscIN = curEscOUT;
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

    void dumpRDAInfo(Function &F, RDAMap &IN, RDAMap &OUT)
    {
      cout << "Function \"" << F.getName() << "\"\n";
      for (auto &pair : IN)
      {
        cout << "INSTRUCTION: " << *pair.first << "\n***************** IN\n{\n";

        for (auto &defPair : pair.second)
        {
          cout << "DEF OF " << *defPair.first << ":\n";
          for (auto *I : defPair.second)
            if (I)
              cout << "  " << *I << "\n";
            else
              cout << "  Argument\n";
        }

        cout << "}\n**************************************\n***************** OUT\n{\n";

        for (auto &defPair : OUT[pair.first])
        {
          cout << "DEF OF " << *defPair.first << ":\n";
          for (auto *I : defPair.second)
            if (I)
              cout << "  " << *I << "\n";
            else
              cout << "  Argument\n";
        }

        errs() << "}\n**************************************\n";
      }
    }

    ConstantInt *getIfIsConstant(Value *operand, RDASet &curIN)
    {
      ConstantInt *constant = nullptr;

      for (auto *def : curIN[operand])
      {
        // def may be PASSED_IN, which means the operand may be defined outside the function
        if (def == PASSED_IN)
          return nullptr;

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
          builder.CreateCall(curModule->getFunction("CAT_set"), std::vector<Value *>({callInst->getOperand(0), newOperand}));
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

        builder.CreateCall(curModule->getFunction("CAT_set"), std::vector<Value *>({callInst->getOperand(0), newOperand}));
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

        // first check if the data is constant
        // if it is then we don't need to check the cache
        if (!constant)
          continue;

        callInst->replaceAllUsesWith(constant);
        deleteList.push_back(callInst);
      }

      for (auto I : deleteList)
        I->eraseFromParent();

      return deleteList.size() > 0;
    }

    bool consecSetEli(Function &F, RDAMap &IN)
    {
      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      for (auto &B : F)
        for (auto &I : B)
          instructions.push_back(&I);

      for (unsigned long i = 0; i < instructions.size() - 1; i++)
      {
        auto *I = instructions[i];
        if (!isa<CallInst>(I) || !isa<CallInst>(instructions[i + 1]))
          continue;
        auto *callInst1 = cast<CallInst>(I);
        auto calledName1 = callInst1->getCalledFunction()->getName();

        auto *callInst2 = cast<CallInst>(instructions[i + 1]);
        auto calledName2 = callInst2->getCalledFunction()->getName();

        if (!calledName2.equals("CAT_set"))
          continue;
        if (!(calledName1.equals("CAT_set") || calledName1.equals("CAT_add") || calledName1.equals("CAT_sub")))
          continue;

        if (callInst1->getOperand(0) == callInst2->getOperand(0))
          deleteList.push_back(callInst1);
      }

      for (auto I : deleteList)
        I->eraseFromParent();

      return deleteList.size() > 0;
    }

    bool deadCodeEli(Function &F, RDAMap &IN)
    {
      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      std::set<Instruction *> argumets;
      DCEMap dceMap;
      // add arguments to the set
      // for (auto &arg : F.args())
      //   argumets.insert(&arg);
      for (auto &B : F)
        for (auto &I : B)
        {
          instructions.push_back(&I);
          if (!isa<CallInst>(I))
            continue;

          auto *callInst = cast<CallInst>(&I);
          auto calledName = callInst->getCalledFunction()->getName();
          // register the call instruction if it is a CAT_add, CAT_sub or CAT_set, which may be deleted by DCE
          if ((calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set")) &&
              !isa<Argument>(callInst->getArgOperand(0)) &&
              escIN[&I].find(callInst->getArgOperand(0)) == escIN[&I].end())
            dceMap[callInst] = false;
        }

      for (auto *I : instructions)
      {

        if (isa<ReturnInst>(I))
        {
          // if return void, then no need to check the return value
          if (I->getNumOperands() == 0)
            continue;
          // mark the def of the return value as alive
          for (auto *def : IN[I][I->getOperand(0)])
            if (dceMap.find(def) != dceMap.end())
              dceMap[def] = true;
        }

        // check dependencies of the call instruction if it's a CAT_add, CAT_sub or CAT_get
        if (!isa<CallInst>(I))
          continue;
        auto *callInst = cast<CallInst>(I);
        auto calledName = callInst->getCalledFunction()->getName();

        if (calledName.equals("CAT_add") || calledName.equals("CAT_sub"))
        {
          auto *op1 = callInst->getOperand(1), *op2 = callInst->getOperand(2);
          // mark the def of the operands (only ones registered in map) as alive
          for (auto *def : IN[I][op1])
            if (dceMap.find(def) != dceMap.end())
              dceMap[def] = true;
          for (auto *def : IN[I][op2])
            if (dceMap.find(def) != dceMap.end())
              dceMap[def] = true;
        }
        else if (calledName.equals("CAT_get"))
        {
          for (auto *def : IN[I][callInst->getOperand(0)])
            if (dceMap.find(def) != dceMap.end())
              dceMap[def] = true;
        }
        else if (!calledName.equals("CAT_set") &&
                 !calledName.equals("CAT_new") &&
                 !calledName.equals("CAT_destroy") &&
                 !calledName.equals("printf") &&
                 !calledName.startswith("llvm.lifetime") &&
                 !calledName.equals("puts"))
        {
          // misc function call
          // mark the def of the arguments and all the escaped values as alive
          for (auto *op : escIN[I])
            for (auto *def : IN[I][op])
              if (dceMap.find(def) != dceMap.end())
                dceMap[def] = true;

          for (auto &op : callInst->operands())
            for (auto *def : IN[I][op])
              if (dceMap.find(def) != dceMap.end())
                dceMap[def] = true;
        }
      }

      bool changed = false;
      // delete the call instructions that are registered and marked as dead
      for (auto &pair : dceMap)
        if (!pair.second)
        {
          changed = true;
          pair.first->eraseFromParent();
        }

      if (!changed)
        changed |= consecSetEli(F, IN);

      return changed;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction(Function &F) override
    {
      curFunc = &F;
      std::queue<BasicBlock *> toBeAnalyzed;

      // initialize the queue with all the blocks without predecessors
      for (auto &B : F)
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

      // dumpRDAInfo(F, IN, OUT);

      bool changed = false;

      changed |= constantFoldAndAlgSimp();
      changed |= constantProp();

      // only do DCE when no constant folding or propagation is done
      if (!changed)
        changed |= deadCodeEli(F, IN);

      return changed;
    }

    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override
    {
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
