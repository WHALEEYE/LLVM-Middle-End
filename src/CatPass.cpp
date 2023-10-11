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

namespace
{
  typedef std::map<Value *, std::set<CallInst *>> RDASet;
  typedef std::map<Instruction *, std::map<Value *, std::set<CallInst *>>> RDAMap;
  typedef std::map<CallInst *, bool> DCEMap;

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

    bool RDAinBB(BasicBlock &BB, RDAMap &IN, RDAMap &OUT)
    {
      RDASet curIN, curOUT;
      // create two temporary sets for comparing old OUT and new OUT
      std::unordered_set<CallInst *> oldOut, newOut;
      bool firstTime = true;

      // if the block already have OUT, store it for further comparison
      if (OUT.find(BB.getTerminator()) != OUT.end())
      {
        firstTime = false;
        for (auto &pair : OUT[BB.getTerminator()])
          for (auto *I : pair.second)
            oldOut.insert(I);
      }

      // merge all the predecessors' OUTs into IN of the current block
      if (!predecessors(&BB).empty())
        for (auto *PB : predecessors(&BB))
        {
          // if the predecessor is not analyzed yet, skip
          if (OUT.find(PB->getTerminator()) == OUT.end())
            continue;

          for (auto &pair : OUT[PB->getTerminator()])
            for (auto *I : pair.second)
              curIN[pair.first].insert(I);
        }

      // calculate IN and OUT for each instruction in the current block
      for (auto &I : BB)
      {
        IN[&I] = curIN;
        curOUT = curIN;

        if (auto *callInst = dyn_cast<CallInst>(&I))
        {
          Value *gen;
          auto calledName = callInst->getCalledFunction()->getName();
          if (calledName.equals("CAT_new"))
          {
            gen = callInst;
            curOUT[gen] = std::set<CallInst *>();
            curOUT[gen].insert(callInst);
          }
          else if (calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set"))
          {
            gen = callInst->getArgOperand(0);
            curOUT[gen] = std::set<CallInst *>();
            curOUT[gen].insert(callInst);
          }
        }

        OUT[&I] = curOUT;
        curIN = curOUT;
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
            errs() << *I << "\n";

        errs() << "}\n**************************************\n***************** OUT\n{\n";

        for (auto &defPair : OUT[pair.first])
          for (auto *I : defPair.second)
            errs() << *I << "\n";

        errs() << "}\n**************************************\n";
      }
    }

    Value *getIfIsConstant(Value *operand, RDASet &curIN)
    {
      Value *constant = nullptr;
      for (auto def : curIN[operand])
      {
        auto *callInst = cast<CallInst>(def);
        auto calledName = callInst->getCalledFunction()->getName();
        Value *newConstant;

        if (calledName.equals("CAT_new"))
          newConstant = callInst->getOperand(0);
        else if (calledName.equals("CAT_set"))
          newConstant = callInst->getOperand(1);
        else
          return nullptr;

        if (!constant)
          constant = newConstant;
        else if (!isa<ConstantInt>(constant) || !isa<ConstantInt>(newConstant))
          return nullptr;
        else if (cast<ConstantInt>(constant)->getValue() == cast<ConstantInt>(newConstant)->getValue())
          continue;
        else
          return nullptr;
      }

      return constant;
    }

    void constantFoldAndAlgSimp(Function &F, RDAMap &IN)
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
    }

    void constantProp(Function &F, RDAMap &IN)
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
    }

    void deadCodeEli(Function &F, RDAMap &IN)
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
          if (calledName.equals("CAT_add") || calledName.equals("CAT_sub") || calledName.equals("CAT_set"))
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

      // delete the call instructions that are registered and marked as dead
      for (auto &pair : dceMap)
        if (!pair.second)
          pair.first->eraseFromParent();
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction(Function &F) override
    {
      RDAMap IN, OUT;
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
        if (RDAinBB(*BB, IN, OUT))
          for (auto *suc : successors(BB))
            toBeAnalyzed.push(suc);
      }
      // printRDAResult(F, IN, OUT);

      // dead code elimination, must be done right after RDA
      deadCodeEli(F, IN);

      constantFoldAndAlgSimp(F, IN);
      constantProp(F, IN);
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override
    {
      // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      AU.setPreservesAll();
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
