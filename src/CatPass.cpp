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

namespace
{
  typedef std::map<Value *, std::set<Instruction *>> RDASet;
  typedef std::map<Instruction *, RDASet> RDAMap;
  typedef std::map<Value *, std::set<Value *>> AliasSet;
  typedef std::map<Instruction *, AliasSet> AliasMap;
  typedef std::map<Instruction *, bool> DCEMap;

  struct CAT : public FunctionPass
  {
    static char ID;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization(Module &M) override
    {
      // errs() << "Hello LLVM World at \"doInitialization\"\n" ;
      return false;
    }

    bool RDAinBB(BasicBlock &BB, RDAMap &IN, RDAMap &OUT, AliasMap &aliIN, AliasMap &aliOUT)
    {
      RDASet curIN, curOUT;
      AliasSet curAliIN, curAliOUT;
      // create two temporary sets for comparing old OUT and new OUT
      std::unordered_set<Instruction *> oldOut, newOut;
      AliasSet oldAliOUT;
      bool firstTime = true;

      // if the block already have OUT, store it for further comparison
      if (OUT.find(BB.getTerminator()) != OUT.end())
      {
        firstTime = false;
        for (auto &pair : OUT[BB.getTerminator()])
          for (auto *I : pair.second)
            oldOut.insert(I);
        // also store the aliasing information
        oldAliOUT = aliOUT[BB.getTerminator()];
      }

      // merge the predecessors' information
      if (!predecessors(&BB).empty())
      {
        for (auto *PB : predecessors(&BB))
        {
          // if the predecessor is not analyzed yet, skip
          if (OUT.find(PB->getTerminator()) == OUT.end())
            continue;

          // merge the reaching definitions
          for (auto &pair : OUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curIN[pair.first].insert(I);

          // merge the aliasing information
          for (auto &pair : aliOUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curAliIN[pair.first].insert(I);
        }
      }
      else
      {
        // if the block has no predecessors, then it's the entry block
        // initialize the IN of the entry block to the arguments
        for (auto &arg : BB.getParent()->args())
        {
          curIN[&arg] = std::set<Instruction *>();
          curIN[&arg].insert(PASSED_IN);
        }
      }

      // calculate IN and OUT for each instruction in the current block
      for (auto &I : BB)
      {
        IN[&I] = curIN;
        curOUT = curIN;
        aliIN[&I] = curAliIN;
        curAliOUT = curAliIN;

        // arguments might be assigned in CAT_get, CAT_add, CAT_sub, or in functions
        if (auto *callInst = dyn_cast<CallInst>(&I))
        {
          Value *gen = nullptr;
          auto calledName = callInst->getCalledFunction()->getName();
          if (calledName.equals("CAT_new"))
          {
            gen = callInst;
            curOUT[gen] = std::set<Instruction *>();
            curOUT[gen].insert(callInst);
            // add itself to its own aliasing set, in case that it's not inside yet
            curAliOUT[gen].insert(gen);
          }
          else if (calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set"))
          {
            gen = callInst->getArgOperand(0);
            curOUT[gen] = std::set<Instruction *>();
            curOUT[gen].insert(callInst);
          }
          else if (!calledName.equals("CAT_get") && !calledName.equals("CAT_destroy") && !calledName.equals("printf"))
          {
            // dealing with references that are passed into functions
            for (auto &op : callInst->operands())
            {
              gen = op.get();
              if (!gen->getType()->isPointerTy())
                continue;
              curOUT[gen] = std::set<Instruction *>();
              curOUT[gen].insert(callInst);
            }
          }
          // for all the other aliases, add the call instruction to their reaching definitions
          // because its possible that their values are changed by this call
          if (gen)
            for (auto *aliased : curAliOUT[gen])
              curOUT[aliased].insert(callInst);
        }
        else if (I.getType()->isPointerTy() && isa<PHINode>(I))
        {
          // aliasing/multiple definition may be happening
          // for now we only consider the case where the definition is a pointer (CAT are all pointers)
          // add the aliasing information, no need to add the reaching definitions (because no CAT_data is changed or created)
          auto *phiNode = cast<PHINode>(&I);
          // remove the alias from all the sets that contain it
          for (auto *aliased : curAliIN[phiNode])
            curAliOUT[aliased].erase(phiNode);

          // clear the current set, initialize it with itself
          curAliOUT[phiNode] = std::set<Value *>();
          curAliOUT[phiNode].insert(phiNode);

          curOUT[phiNode] = std::set<Instruction *>();
          // for each incoming value, add the aliasing information and merge their reaching definitions
          for (auto &op : phiNode->incoming_values())
          {
            curOUT[phiNode].insert(curIN[op.get()].begin(), curIN[op.get()].end());

            for (auto *aliased : curAliIN[op.get()])
            {
              curAliOUT[phiNode].insert(aliased);
              curAliOUT[aliased].insert(phiNode);
            }
          }
        }
        OUT[&I] = curOUT;
        curIN = curOUT;
        aliOUT[&I] = curAliOUT;
        curAliIN = curAliOUT;
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

    void printRDAResult(Function &F, RDAMap &IN, RDAMap &OUT)
    {
      errs() << "Function \"" << F.getName() << "\"\n";
      for (auto &pair : IN)
      {
        errs() << "INSTRUCTION:   " << *pair.first << "\n***************** IN\n{\n";

        for (auto &defPair : pair.second)
          for (auto *I : defPair.second)
            if (I)
              errs() << *I << "\n";
            else
              errs() << "Argument\n";

        errs() << "}\n**************************************\n***************** OUT\n{\n";

        for (auto &defPair : OUT[pair.first])
          for (auto *I : defPair.second)
            if (I)
              errs() << *I << "\n";
            else
              errs() << "Argument\n";

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
          else if (calledName.equals("CAT_set")){
            candidate = callInst->getOperand(1);
            errs() << "candidate: " << *candidate << "\n";
            errs() << "isConstant: " << isa<ConstantInt>(candidate) << "\n";}
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

    bool constantFoldAndAlgSimp(Function &F, RDAMap &IN, AliasMap &aliIN)
    {
      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      for (auto &B : F)
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

        // algorithmic simplification, sub x x = 0
        // if (calledName.equals("CAT_sub") && callInst->getOperand(1) == callInst->getOperand(2))
        // {
        //   IRBuilder<> builder(callInst);
        //   builder.CreateCall(F.getParent()->getFunction("CAT_set"), std::vector<Value *>({callInst->getOperand(0), ConstantInt::get(Type::getInt64Ty(F.getContext()), 0)}));
        //   deleteList.push_back(callInst);
        //   continue;
        // }

        // check if all the definitions of the operands that reach the call instruction are constant
        auto op1 = callInst->getOperand(1);
        auto op2 = callInst->getOperand(2);
        auto *constant1 = getIfIsConstant(op1, IN[I]), *constant2 = getIfIsConstant(op2, IN[I]);
        if (!constant1 && !constant2)
          continue;

        IRBuilder<> builder(callInst);
        Value *newOperand;
        // if both operands are constant, constant fold
        if (constant1 && constant2)
          newOperand = calledName.equals("CAT_add") ? builder.CreateAdd(constant1, constant2) : builder.CreateSub(constant1, constant2);
        // if one of the operands is constant 0, then we can do the algebraic simplification
        else if (!constant1 && isa<ConstantInt>(constant2) && cast<ConstantInt>(constant2)->getValue() == 0)
          newOperand = builder.CreateCall(F.getParent()->getFunction("CAT_get"), std::vector<Value *>({op1}));
        else if (!constant2 && isa<ConstantInt>(constant1) && cast<ConstantInt>(constant1)->getValue() == 0 && calledName.equals("CAT_add"))
          // if the operation is CAT_sub and the second operand is not constant, then we can't simplify it because we need to do negation
          newOperand = builder.CreateCall(F.getParent()->getFunction("CAT_get"), std::vector<Value *>({op2}));
        else
          continue;

        builder.CreateCall(F.getParent()->getFunction("CAT_set"), std::vector<Value *>({callInst->getOperand(0), newOperand}));
        deleteList.push_back(callInst);
      }
      for (auto *I : deleteList)
        I->eraseFromParent();

      return deleteList.size() > 0;
    }

    bool constantProp(Function &F, RDAMap &IN, AliasMap &aliIN)
    {
      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      for (auto &B : F)
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

    bool deadCodeEli(Function &F, RDAMap &IN)
    {
      std::vector<CallInst *> deleteList;
      std::vector<Instruction *> instructions;
      DCEMap dceMap;
      for (auto &B : F)
        for (auto &I : B)
        {
          instructions.push_back(&I);
          if (!isa<CallInst>(I))
            continue;
          auto *callInst = cast<CallInst>(&I);
          auto calledName = callInst->getCalledFunction()->getName();
          // register the call instruction if it is a CAT_add, CAT_sub or CAT_set, which may be deleted by DCE
          // DCE won't eliminate CAT_new and CAT_get
          // DCE won't eliminate CAT_add, CAT_sub and CAT_set if the first operand is an argument
          if ((calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set")) && !isa<Argument>(callInst->getArgOperand(0)))
            dceMap[callInst] = false;
        }

      for (auto *I : instructions)
      {
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
        else
          continue;
      }

      bool changed = false;
      // delete the call instructions that are registered and marked as dead
      for (auto &pair : dceMap)
        if (!pair.second)
        {
          changed = true;
          pair.first->eraseFromParent();
        }
      return changed;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction(Function &F) override
    {
      RDAMap IN, OUT;
      AliasMap aliIN, aliOUT;
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
        if (RDAinBB(*BB, IN, OUT, aliIN, aliOUT))
          for (auto *suc : successors(BB))
            toBeAnalyzed.push(suc);
      }
      // printRDAResult(F, IN, OUT);

      bool changed = false;

      changed |= constantFoldAndAlgSimp(F, IN, aliIN);
      changed |= constantProp(F, IN, aliIN);

      // to avoid all CAT_set being eliminated by DCE (so the signature will also be killed)
      // we only do DCE when there is no further constant optimization
      // DCE will not bring new optimization points to fold and propagation
      // if (!changed)
      //   changed |= deadCodeEli(F, IN);

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
