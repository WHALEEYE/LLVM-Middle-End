#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include <map>
#include <set>
#include <unordered_set>
#include <queue>

using namespace llvm;

namespace
{
  struct Sets
  {
    std::map<Value *, std::set<CallInst *>> in, out;
  };

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

    bool RDAinBB(BasicBlock &BB, std::map<Instruction *, Sets *> &inNOut)
    {
      Sets *sets = new Sets();
      // create two temporary sets for comparing old OUT and new OUT
      std::unordered_set<CallInst *> oldOut, newOut;
      bool firstTime = true;

      // if the block already have OUT, store it for further comparison
      if (inNOut.find(BB.getTerminator()) != inNOut.end())
      {
        firstTime = false;
        for (auto &pair : inNOut[BB.getTerminator()]->out)
          for (auto *I : pair.second)
            oldOut.insert(I);
      }

      // merge all the predecessors' OUTs into IN of the current block
      if (!predecessors(&BB).empty())
        for (auto *PB : predecessors(&BB))
        {
          // if the predecessor is not analyzed yet, skip
          if (inNOut.find(PB->getTerminator()) == inNOut.end())
            continue;

          auto *predSets = inNOut[PB->getTerminator()];
          for (auto &pair : predSets->out)
            for (auto *I : pair.second)
            {
              sets->in[pair.first].insert(I);
              newOut.insert(I);
            }
        }

      // calculate OUT for each instruction the current block
      for (auto &I : BB)
      {
        sets->out = sets->in;
        if (isa<CallInst>(I))
        {
          auto *callInst = dyn_cast<CallInst>(&I);
          Function *calledFunction = callInst->getCalledFunction();
          if (calledFunction)
          {
            Value *gen;
            if (calledFunction->getName().equals("CAT_new"))
            {
              gen = callInst;
              sets->out[gen] = std::set<CallInst *>();
              sets->out[gen].insert(callInst);
            }
            else if (calledFunction->getName().equals("CAT_add") || calledFunction->getName().equals("CAT_sub") || calledFunction->getName().equals("CAT_set"))
            {
              gen = callInst->getArgOperand(0);
              sets->out[gen] = std::set<CallInst *>();
              sets->out[gen].insert(callInst);
            }
          }
        }
        inNOut[&I] = sets;
        sets = new Sets();
        sets->in = inNOut[&I]->out;
      }

      // if the block is analyzed for the first time, then we need to add its successors to the queue
      if (firstTime)
        return true;

      // the block is analyzed before, so we need to compare the old OUT with the new OUT
      for (auto &pair : inNOut[BB.getTerminator()]->out)
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

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction(Function &F) override
    {
      std::map<Instruction *, Sets *> inNOut;
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
        if (RDAinBB(*BB, inNOut))
          for (auto *suc : successors(BB))
            toBeAnalyzed.push(suc);
      }

      errs() << "Function \"" << F.getName() << "\"\n";
      for (auto &pair : inNOut)
      {
        errs() << "INSTRUCTION:   " << *pair.first << "\n***************** IN\n{\n";

        for (auto &defPair : pair.second->in)
          for (auto *I : defPair.second)
            errs() << *I << "\n";

        errs() << "}\n**************************************\n***************** OUT\n{\n";

        for (auto &defPair : pair.second->out)
          for (auto *I : defPair.second)
            errs() << *I << "\n";

        errs() << "}\n**************************************\n";
      }
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
