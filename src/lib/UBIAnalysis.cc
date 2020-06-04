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
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/BasicBlock.h"
#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>
#include <fstream>
#include <time.h>
#include <cstring>
#include <algorithm>

#include "json.hpp"
#include "UBIAnalysis.h"
#include "CallGraph.h"
#include "Config.h"
#include "QualifierAnalysis.h"

using namespace llvm;
//#define TEST_RANK
#define MAIN_ANALYSIS
//#define CG_DEBUG
//#define REST_F
//#define _PRINT_STMAP
// Command line parameters.
cl::list<std::string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
    "verbose-level", cl::desc("Print information at which verbose level"),
    cl::init(0));

cl::opt<bool> UniAnalysis(
    "ubi-analysis",
    cl::desc("Analysis uninitialized pointer dereference"),
    cl::NotHidden, cl::init(false));

GlobalContext GlobalCtx;
enum WarnType {FUNCTION_PTR, NORMAL_PTR, DATA, OTHER};
std::unordered_map<int ,std::string> eToS = {{0, "FUNCTION_PTR"}, {1, "NORMAL_PTR"}, {2, "DATA"}, {3, "OTHER"}};
enum WarnType getWarnType(llvm::Function *F, const std::string warning);
void IterativeModulePass::run(ModuleList &modules) {
    //std::ofstream fout;
    //fout.open("pointertime.txt");

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

    //adding the intermediate step to initialize circulate functions
    collectRemaining();

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
    //SetEntryFuncs(GCtx->EntryFuncs);
    //SetManualSummarizedFuncs(GCtx->ManualSummaries);
}

void InitReadyFunction(GlobalContext *Ctx) {
    for (auto ml : Ctx->Modules) {
        for (Function &f : *ml.first) {
            Function *F = &f;
            if (!F->empty()) {
                //initialize the readylist;
                if (Ctx->CallMaps.find(F) == Ctx->CallMaps.end()) {
                    // OP << "readylist insert function " << F->getName().str() << "\n";
                    Ctx->ReadyList.insert(F);
                } 
                #ifdef NON_REC
                else {
                    // non-recursive
                    if (Ctx->CallMaps[F].count(F) != 0) {
                        Ctx->ReadyList.insert(F);
                    }
                }
                #endif
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
	/*
        LLVMContext *LLVMCtx = new LLVMContext();
        std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);
        if (M == NULL) {
            OP << argv[0] << ": error loading file '"
               << InputFilenames[i] << "'\n";
            continue;
        }
        Module *Module = M.release();
	//StringRef MName = StringRef(strdup(InputFilenames[i].data()));
	//errs()<<"Module "<<MName.str()<<"\n";
	
        for (Module::iterator f = Module->begin(), fe = Module->end(); f != fe; ++f) {
	    
            Function *F = &*f;
            calculateType(F);
        }*/
	
        std::ifstream jsonFile;
        jsonFile.open(InputFilenames[i], std::ios::in);
        std::string nameStr = InputFilenames[i];
        
        std::string name = nameStr.substr(0, nameStr.find("."));
        std::string newName = name + "-bcreduce.json";
	newName = "reduce/"+newName;
        std::ofstream newJsonFile;
        newJsonFile.open(newName, std::ios::app);       

        std::string json_str = "";
        std::string err;
	std::string bc_str = "";
	std::getline(jsonFile, bc_str);
        while (std::getline(jsonFile, json_str)) {
	    //json_str.erase(std::remove(json_str.begin(), json_str.end(), '\n'), json_str.end()); 
	    //errs()<<"json_str: "<<json_str<<"\n";	
            auto jsonObj = nlohmann::json::parse(json_str);
            std::string moduleName = jsonObj["bc"].dump();
	    //errs()<<"moduleName : "<<moduleName<<"\n";
	    moduleName.erase(std::remove(moduleName.begin(), moduleName.end(), '\"'), moduleName.end());
            std::string funcName = jsonObj["function"].dump();
            std::string warning = jsonObj["warning"].dump();        
	    funcName.erase(std::remove(funcName.begin(), funcName.end(), '\"'), funcName.end());	
	    warning.erase(std::remove(warning.begin(), warning.end(), '\"'), warning.end());
	    //errs()<<"Function: "<<funcName;
	    //errs()<<"warning: "<<warning<<"\n";
            LLVMContext *LLVMCtx = new LLVMContext();
	    //OP<<"2\n";
            std::unique_ptr<Module> M = parseIRFile(moduleName, Err, *LLVMCtx);
     	    //OP<<"3\n";
	    if (M == NULL) {
     		 OP << argv[0] << ": error loading file '"
        		<< moduleName << "'\n";
      			break;
    		}
	    Module *Module = M.release();       
    	    //OP<<"4\n";
		        
	    for (Module::iterator f = Module->begin(), fe = Module->end(); f != fe; ++f) {
                Function *F = &*f;
                //calculateType(F);
                
                if (funcName == F->getName().str())
                {
		    std::set<string> relatedBCs;
		    relatedBC.clear();
		    relatedBC.insert(F->getParent()->getName().str());
		    getRelatedBC(F, warning, relatedBC);

		    for(auto item : relatedBCs)
		    {
       			 newJsonFile<<item<<":";
    		    }
		    newJsonFile<<"\n";
		    newJsonFile<<"json_str";
                }
                
            }
        }
        jsonFile.close();
        newJsonFile.close();

        //StringRef MName = StringRef(strdup(InputFilenames[i].data()));
        //GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
        //GlobalCtx.ModuleMaps[Module] = InputFilenames[i];
    }
#ifdef TEST_RANK
    // Main workflow
    LoadStaticData(&GlobalCtx);

    // Build global callgraph.
    CallGraphPass CGPass(&GlobalCtx);
    CGPass.run(GlobalCtx.Modules);
    #ifdef _PRINT_STMAP
    OP<<"structMap:\n";
    GlobalCtx.structAnalyzer.printStructInfo();
    #endif
#ifdef CG_DEBUG
    //print the result:
    OP << "Call graph:\n";
    for (auto i : GlobalCtx.CallMaps) {
        OP << i.first->getName().str() << " calls: ";
        for (Function *F : i.second) {
            OP << F->getName().str() << "/";
        }
        OP << "\n";
    }
    for (auto i : GlobalCtx.CalledMaps) {
        OP << i.first->getName().str() << " called by: ";
        for (Function *F : i.second) {
            OP << F->getName().str() << "/";
        }
        OP << "\n";
    }
#endif
    // OP << "\nRemained Function:";
    for (auto i : GlobalCtx.CallMaps) {
        GlobalCtx.RemainedFunction[i.first] = i.second.size();
    }
    //print the function summary
    
	


    if (UniAnalysis) {
        InitReadyFunction(&GlobalCtx);
        OP << GlobalCtx.Visit.size() << " functions in total.\n";
        QualifierAnalysis QAPass(&GlobalCtx);
        QAPass.run(GlobalCtx.Modules);
    }
    //for (auto sum : GlobalCtx.FSummaries)
    //{
//	OP<<sum.first<<": "<<sum.first->getName().str()<<"\n";
  //  }
    //print the num of remained funciton
#ifdef REST_F
    std::set<Function*> fset;
    unsigned remained = 0;
    for (auto ml : GlobalCtx.Modules) {
        for (Function &f = *ml.first) {
            Function *F = &f;
            if(GlobalCtx.Visit.find(F) != GlobalCtx.Visit.end() && (!GlobalCtx.Visit[F])) {
                fset.insert(F);
                OP << "@Function " << F->getName().str() << " owns " << GlobalCtx.RemainedFunction[F] << " calles remained.\n";
                int count = 1;
                for (auto cf : GlobalCtx.CallMaps[F]) {
                    if (!GlobalCtx.Visit[cf]) {
                        OP << "--" << count++ << ". " << f->getName().str() << "\n";
                    }
                }
            }
        }
    }
    OP << "# of remained function = " << fset.size() << "\n";
#endif
#endif
    return 0;
}
void getRelatedBC(llvm::Function *F, const std::string warning, std::set<string> &relatedBC) {
    for (inst_iterator itr = inst_begin(*F), ite = inst_end(*F); itr != ite; ++itr) {
	auto inst = itr.getInstructionIterator();
        llvm::Instruction *I = &*inst;

        std::string insStr;
        llvm::raw_string_ostream rso(insStr);
        I->print(rso);

	if (insStr == warning) {
	    switch (I -> getOpcode()) {
		case Instruction::Call: {
		  if (CallInst *CI = dyn_cast<CallInst>(I)) {
			if (CI->getCalledFunction()) {
			    relatedBC.insert(CI->getCalledFunction()->getName().str());
			}
		    }
		}//case Call

	    }
	}
    }
}

enum WarnType getWarnType(llvm::Function *F, const std::string warning)
{
    for (inst_iterator itr = inst_begin(*F), ite = inst_end(*F); itr != ite; ++itr) {
        auto inst = itr.getInstructionIterator();
        llvm::Instruction *I = &*inst;

        std::string insStr;
            llvm::raw_string_ostream rso(insStr);
            I->print(rso);

        if (insStr == warning)
        {
             switch (I -> getOpcode()) {
            case Instruction::Add:
		case Instruction::IntToPtr:
		case Instruction::BitCast:
		case Instruction::Trunc:
		case Instruction::SExt:
		case Instruction::ZExt:
		case Instruction::Select:
		case Instruction::Alloca:
                        case Instruction::FAdd:
                        case Instruction::Sub:
                        case Instruction::FSub:
                        case Instruction::Mul:
                        case Instruction::FMul:
                        case Instruction::SDiv:
                        case Instruction::UDiv:
                        case Instruction::FDiv:
                        case Instruction::SRem:
                        case Instruction::URem:
                        case Instruction::And:
                        case Instruction::Or:
                        case Instruction::Xor:
                        case Instruction::LShr:
                        case Instruction::AShr:
                        case Instruction::Shl:
            case Instruction::Switch:
            case Instruction::PHI:
            case Instruction::GetElementPtr:
            case Instruction::ICmp:
            case Instruction::Load: {
                Type *Ty = I->getType();
                if (PointerType * PT = dyn_cast<PointerType>(Ty)) {
                    do {
                        Type *ptdTy = PT->getElementType();
                        if (ptdTy->isFunctionTy()) {
                            return FUNCTION_PTR;
                        }
                        Ty = ptdTy;
                     }while ((PT = dyn_cast<PointerType>(Ty)));
                    return NORMAL_PTR;
                }
                else {
                    return DATA;
                }
            }//Load
		case Instruction::Br:
		{
			if(I->getNumOperands() == 3)
			{
				Type *Ty = I->getOperand(0)->getType();
	                	if (PointerType * PT = dyn_cast<PointerType>(Ty)) {
        	            	do {
                	        	Type *ptdTy = PT->getElementType();
                       			if (ptdTy->isFunctionTy()) {
                            			return FUNCTION_PTR;
                        		}
        	                	Ty = ptdTy;
                	     	}while ((PT = dyn_cast<PointerType>(Ty)));
                	    	return NORMAL_PTR;
	                	}
        	        	else {
                	    		return DATA;
               		 	}

			}
		}
            case Instruction::Call:{
                return NORMAL_PTR;
            }
            default:
            {
                errs()<<"Do not deal with this warning: "<<warning<<"\n";
            }
            }//switch
        }
    }
    return OTHER;
}

