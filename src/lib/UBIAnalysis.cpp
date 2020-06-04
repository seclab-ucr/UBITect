#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Utils/FunctionComparator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/DebugInfo.h"
#include <llvm/IR/InstIterator.h>
#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>
#include <fstream>
#include <time.h>
#include <cstring>
#include <typeinfo>

#include "UBIAnalysis.h"
#include "CallGraph.h"
#include "Config.h"
#include "QualifierAnalysis.h"


using namespace llvm;
// Command line parameters.
cl::list<std::string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<bool> UniAnalysis(
    "ubi-analysis",
    cl::desc("Analysis uninitialized pointer dereference"),
    cl::NotHidden, cl::init(false));

GlobalContext GlobalCtx;

void IterativeModulePass::run(ModuleList &modules) {

    ModuleList::iterator i, e;
    OP << "[" << ID << "] Initializing " << modules.size() << " modules ";
    bool again = true;
    while (again) {
        again = false;
        for (i = modules.begin(), e = modules.end(); i != e; ++i) {
            again |= doInitialization(i->first);
            OP << ".";
        }
    }
    OP << "\n";

    //calculate functions not enrolled in loops
    unsigned iter = 0, changed = 1;
    while (changed) {
        ++iter;
        changed = 0;
        for (i = modules.begin(), e = modules.end(); i != e; ++i) {
            OP << "[" << ID << " / " << iter << "] ";
            OP << "[" << i->second << "]\n";
            
            bool ret = doModulePass(i->first);
            if (ret) {
                ++changed;
                OP << "\t [CHANGED]\n";
            } else
                OP << "\n";
        }
        OP << "[" << ID << "] Updated in " << changed << " modules.\n";
    }
 
    //calculate the scc iteratively
    //adding the intermediate step to initialize circulate functions
    collectRemaining();
    //do module pass again and deal with callers of loop enrolled functions
    changed = 1;
    while (changed) {
        ++iter;
        changed = 0;
        for (i = modules.begin(), e = modules.end(); i != e; ++i) {
            OP << "[" << ID << " / " << iter << "] ";
            OP << "[" << i->second << "]\n"; 

            bool ret = doModulePass(i->first);
            if (ret) { 
                ++changed;
                OP << "\t [CHANGED]\n";
            } else 
                OP << "\n";
        }
        OP << "[" << ID << "] Updated in " << changed << " modules.\n";
    }
    //Finalization
    OP << "[" << ID << "] Postprocessing ...\n";
    again = true;
    while (again) {
        again = false;
        for (i = modules.begin(), e = modules.end(); i != e; ++i) {
            // TODO: Dump the results.
            again |= doFinalization(i->first);
        }
    }
    OP << "Finalizing ...\n";
    finalize();
    OP << "[" << ID << "] Done!\n\n";
}

void LoadStaticData(GlobalContext *GCtx) {
    // load functions for heap allocations
    SetHeapAllocFuncs(GCtx->HeapAllocFuncs);
    SetInitFuncs(GCtx->InitFuncs);
    SetCopyFuncs(GCtx->CopyFuncs);
    SetTransferFuncs(GCtx->TransferFuncs);
    SetObjSizeFuncs(GCtx->ObjSizeFuncs);
	//SetStrFuncs(GCtx->StrFuncs);
}

void InitReadyFunction(GlobalContext *Ctx) {
    for (auto ml : Ctx->Modules) {
        for (Function &f : *ml.first) {
            Function *F = &f;
            if (!F->empty()) {
                //initialize the readylist;
                if (Ctx->CallMaps.find(F) == Ctx->CallMaps.end()) {
                    Ctx->ReadyList.insert(F);
                } 
                Ctx->Visit[F] = false;
            }
        }
    }
}

int main(int argc, char **argv){
    // Print a stack trace if we signal out.
    sys::PrintStackTraceOnErrorSignal(argv[0]);
    PrettyStackTraceProgram X(argc, argv);

    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

    cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
    SMDiagnostic Err;

    // Loading modules
    OP << "Total " << InputFilenames.size() << " file(s)\n";

    for (unsigned i = 0; i < InputFilenames.size(); ++i) {

        LLVMContext *LLVMCtx = new LLVMContext();
        std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

        if (M == NULL) {
            OP << argv[0] << ": error loading file '"
               << InputFilenames[i] << "'\n";
            continue;
        }

        Module *Module = M.release();
        StringRef MName = StringRef(strdup(InputFilenames[i].data()));
        GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
        GlobalCtx.ModuleMaps[Module] = InputFilenames[i];
    }

    // Main workflow
    LoadStaticData(&GlobalCtx);
    // Build global callgraph.
    CallGraphPass CGPass(&GlobalCtx);
    CGPass.run(GlobalCtx.Modules);
    CGPass.fillCallGraphs();
      
    for (auto i : GlobalCtx.CallMaps) {
        GlobalCtx.RemainedFunction[i.first] = i.second.size();
    }
    
    if (UniAnalysis) {
        InitReadyFunction(&GlobalCtx);
        OP << GlobalCtx.Visit.size() << " functions in total.\n";
        QualifierAnalysis QAPass(&GlobalCtx);
        QAPass.run(GlobalCtx.Modules);
    }
    
    return 0;
}
