#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/PassSupport.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Instruction.h"
#include <cstring>
#include <string>

using namespace llvm;

namespace{
std::string replaceChar(std::string str, char ch1, char ch2);
    struct bbTag : public ModulePass{
        static char ID;
        bbTag() : ModulePass(ID) {};

        bool runOnModule(Module &M) override{
            for (Module::iterator F = M.begin(); F != M.end(); F++)
            {
                unsigned int block_num = 0;
                for (Function::iterator BB = F->begin(); BB != F->end(); BB++)
                {   
                    std::string mName = M.getName().str();
		    mName = replaceChar(mName,'/', '-');
		    BB->setName(mName + "-" + F->getName().str() + "-"  + utostr(block_num++));
		}

            }
            return true;
        }
    };
std::string replaceChar(std::string str, char ch1, char ch2) {
  for (int i = 0; i < str.length(); ++i) {
    if (str[i] == ch1)
      str[i] = ch2;
  }

  return str;
}
}
char bbTag::ID = 0;
static RegisterPass<bbTag> X("bbtag", "Label BB Pass", false, false);

