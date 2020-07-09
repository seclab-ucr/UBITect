//
// Created by ubuntu on 10/22/17.
//

#ifndef UBIANALYSIS_H
#define UBIANALYSIS_H


#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include "llvm/Support/CommandLine.h"

#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <list>
#include <queue>

#include "Common.h"
#include "StructAnalyzer.h"
#include "FunctionSummary.h"

//
// typedefs
//
typedef std::vector< std::pair<llvm::Module*, llvm::StringRef> > ModuleList;
// Mapping module to its file name.
typedef std::unordered_map<llvm::Module*, llvm::StringRef> ModuleNameMap;
// The set of all functions.
typedef llvm::SmallPtrSet<llvm::Function*, 8> FuncSet;
// Mapping from function name to function.
typedef std::unordered_map<std::string, llvm::Function*> NameFuncMap;
typedef llvm::SmallPtrSet<llvm::CallInst*, 8> CallInstSet;
typedef std::unordered_map<std::string, llvm::GlobalVariable*> GObjMap;
typedef llvm::DenseMap<llvm::Function*, CallInstSet> CallerMap;
typedef llvm::DenseMap<llvm::CallInst *, FuncSet> CalleeMap;
//mapping from the function to the functions it calls
typedef std::unordered_map<llvm::Function*, std::set<llvm::Function*>> CallMap;
typedef llvm::DenseMap<llvm::Function *, FuncSet> CalledMap;
typedef std::unordered_map<std::string, FuncSet> FuncPtrMap;

typedef std::unordered_map<llvm::Function *, Summary> FtSummary;
typedef std::unordered_map<llvm::Function*, std::set<llvm::Value*>> FuncHolder;
struct GlobalContext {

    GlobalContext() {}

    // Map global function name to function defination.
    NameFuncMap Funcs;
    std::map<std::string, std::set<llvm::Function*>> nameFuncs;
	
    // Map global object name to object definition
    GObjMap Gobjs;

    // Map function pointers (IDs) to possible assignments
    std::set<llvm::Function*> FPtrs;
    FuncPtrMap FuncPtrs;
    // Functions whose addresses are taken.
    FuncSet AddressTakenFuncs;

    // Map a callsite to all potential callee functions.
    CalleeMap Callees;

    // Conservative mapping for callees for a callsite
    CalleeMap ConsCallees;

    //map the function to the struct which holds the function
    FuncHolder FuncHolders;
    // Map a function to all potential caller instructions.
    CallerMap Callers;

    //Map a function to the functions it calls
    CallMap CallMaps;

    CallMap DirectCallMap;
    //Map a function to the functions who call it
    CalledMap CalledMaps;

    //visit map used in qualifier analysis
    std::map<llvm::Function *, bool> Visit;

    //functions ready for analysis
    std::set<llvm::Function* > ReadyList;
    //calculate the # of called functions of the caller
    std::map<llvm::Function*, int> RemainedFunction;
    std::unordered_set<llvm::Function* > indFuncs;

    std::vector<std::vector<llvm::Function*>> SCC;
    std::set<llvm::Function*> rec;
    std::unordered_map<std::string, std::set<int>> Warnings;
    //FunctionSummary
    FtSummary FSummaries;
    //The number of the uninitialized variables when declared.
    long long numDecl = 0;
    long long numUninit = 0;
    long long fieldDecl = 0;
    long long fieldUninit = 0;
    
    //The # of variables which treat as ubi with intra-procedural analysis
    //uninitArg gives the total # of variables which are uninit while passing to the callee
    long long uninitArg = 0;
    //uninitOut Arg calculate the # of variables which are not uninit if it comes from argument
    long long uninitOutArg = 0;
    //ignoreOutArg calculate the # of variables which are 
    long long ignoreOutArg = 0;

    //For the finalization, change means the summary changes
    std::map<llvm::Function *, bool> ChangeMap;

    // Indirect call instructions.
    std::vector<llvm::CallInst *> IndirectCallInsts;

    // Modules.
    ModuleList Modules;
    ModuleNameMap ModuleMaps;
    std::set<std::string> InvolvedModules;
    // Some manually-summarized functions that initialize
    // values.
    std::set<std::string> HeapAllocFuncs;
    std::set<std::string> CopyFuncs;
    std::set<std::string> InitFuncs;
    std::set<std::string> TransferFuncs;
    std::set<std::string> ObjSizeFuncs;
    std::set<std::string> StrFuncs;
    std::set<std::string> OtherFuncs;
    std::set<std::string> visitedFuncs;

    // StructAnalyzer
    StructAnalyzer structAnalyzer;
    std::map<const llvm::StructType*, std::set<int>> usedField;
};

class IterativeModulePass {
protected:
    GlobalContext *Ctx;
    const char * ID;
public:
    IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
            : Ctx(Ctx_), ID(ID_) { }

    // Run on each module before iterative pass.
    virtual bool doInitialization(llvm::Module *M)
    { return true; }

    // Run on each module after iterative pass.
    virtual bool doFinalization(llvm::Module *M)
    { return true; }

    // Iterative pass.
    virtual bool doModulePass(llvm::Module *M)
    { return false; }

    virtual void run(ModuleList &modules);
//    virtual void collectRemaining(){}
//    virtual void calDepFuncs(){}
//    virtual void finalize(){}
};


#endif //UBIANALYSIS_H

