//
// Created by ubuntu on 2/8/18.
//

#ifndef UBIANALYSIS_QUALIFIERANALYSIS_H
#define UBIANALYSIS_QUALIFIERANALYSIS_H

#include <llvm/Analysis/CallGraph.h>
#include <llvm/IR/BasicBlock.h>

#include "UBIAnalysis.h"
#include "NodeFactory.h"
#include "PtsSet.h"
#include "FunctionSummary.h"

#include <set>
#include <map>
#include <unordered_map>

#define _ID 1
#define _UD 0
#define _UNKNOWN -1
#define UNDEFINE -2

#define _CH 1

typedef std::map<NodeIndex, AndersPtsSet> PtsGraph;
typedef std::map<const llvm::Instruction*, PtsGraph> NodeToPtsGraph;
typedef std::map<const llvm::Instruction*, std::vector<int>> NodeToQualifier;
typedef std::map<const llvm::BasicBlock*, std::vector<int>> BBToQualifier;

//alias set
typedef std::set<NodeIndex> NodeSet;
typedef std::unordered_map<NodeIndex, NodeSet> AAMap;
typedef std::unordered_map<const llvm::Instruction*, AAMap> NodeToAAMap;
enum WarnType {FUNCTION_PTR, NORMAL_PTR, DATA, OTHER};

class QualifierAnalysis : public IterativeModulePass {
private:
    const llvm::DataLayout* DL;
    llvm::Module *module;
    unsigned FCounter;

    //if flag = true then we runn till check, else we run till inference to converge
    bool runOnFunction(llvm::Function *, bool flag);
    void collectConstraintsForGlobals(llvm::Function *, AndersNodeFactory &, PtsGraph &);

    void collectConstraintsForInstruction(const llvm::Instruction*);
    void addConstraintForKMalloc(const llvm::CallInst*, int, int);

    void ptsJoin(PtsGraph&, PtsGraph&);
    //Used by qualifier inference 
    void setGlobalQualies(llvm::Function *, AndersNodeFactory &, NodeToPtsGraph &, int *);
    //void qualiJoin(int *, int *, unsigned);
    //void updateJoin(int *, int *, unsigned);
    //void computeAASet(llvm::Function *, AndersNodeFactory &, NodeToPtsGraph &, NodeToAAMap &, NodeIndex);
    //void updateJoin(int *, int *, unsigned);
    

public:
    QualifierAnalysis(GlobalContext *Ctx_)
            : IterativeModulePass(Ctx_, "QualifierAnalysis"),
              FCounter(0) {}

    virtual bool doModulePass(llvm::Module *);
    virtual bool doInitialization(llvm::Module *);
    virtual bool doFinalization(llvm::Module *);
    void PrintStatistics();
    void collectRemaining();
    //used for recursive function:
    void calSumForRec (std::set<llvm::Function*>&);
    void calSumForScc (std::vector<std::vector<llvm::Function*>>&);
    void calDepFuncs();
    void finalize();
    void getGlobals();
    void run();
};

class FuncAnalysis {
private:
    llvm::Function *F;
    const llvm::DataLayout* DL;
    llvm::Module *M;
    GlobalContext *Ctx;

    AndersNodeFactory nodeFactory;
    NodeToPtsGraph nPtsGraph;
    NodeToPtsGraph inPtsGraph;
    NodeToAAMap nAAMap;

    NodeToQualifier nQualiArray;
    NodeToQualifier nQualiUpdate;
    std::vector<int> qualiReq;
    BBToQualifier inQualiArray;
    BBToQualifier outQualiArray;
    
    Summary fSummary;
    bool printWarning;
    
    std::map<llvm::Instruction*, int *>nUpdate;
    std::set<llvm::Instruction*> VisitIns;
    std::set<int> warningSet;
    std::set<std::string> relatedBC;
    std::unordered_map<int ,std::string> eToS = {{0, "FUNCTION_PTR"}, {1, "NORMAL_PTR"}, {2, "DATA"}, {3, "OTHER"}};
    //statistics:
    std::set<NodeIndex> uninitArg;
    std::set<NodeIndex> uninitOutArg;
    std::set<NodeIndex> ignoreOutArg;

    std::map<NodeIndex, std::set<NodeIndex>> relatedNode;

    void buildPtsGraph();
    void qualiInference();
    void QualifierCheck();
    void computeAASet();
    void calStackVar();
    //utils
    void createNodeForPointerVal(const llvm::Value*, const llvm::Type*, const NodeIndex valNode, PtsGraph &);
    void createInitNodes(PtsGraph &);
    PtsGraph processInstruction(llvm::Instruction*, PtsGraph &);
    NodeIndex processStruct(const llvm::Value*, const llvm::StructType*, const NodeIndex valNode, PtsGraph &);
    void unionPtsGraph(PtsGraph&, const PtsGraph&);
    NodeIndex extendObjectSize(NodeIndex, const llvm::StructType*, PtsGraph&);
    void updateObjectNode(NodeIndex, NodeIndex, PtsGraph&);
    int handleContainerOf(const llvm::Instruction*, int64_t, NodeIndex, PtsGraph&);
    void printRelatedBB(NodeIndex nodeIndex, const llvm::Value*, std::set<const Instruction*> &visit, 
			std::string, int argNo=-1, int field=-1, llvm::Function *Callee=NULL);
    void calculateRelatedBB(NodeIndex , const llvm::Instruction *I, std::set<NodeIndex> &visit, 
                                        std::set<const BasicBlock *> &blacklist, std::set<const BasicBlock *> &whitelist);
    void calculateBLForUse(const llvm::Instruction *I, std::set<const BasicBlock *> &blacklist);
    void handleGEPConstant(const ConstantExpr *ce, PtsGraph &in);
    void addRelatedBC(llvm::Instruction*, NodeIndex , llvm::Function *Callee=NULL);

    //Used by qualifier inference 
    void computeQualifier(llvm::Instruction *, std::vector<int> &, std::vector<int>&);
    void setGlobalQualies(std::vector<int> &);
    void qualiJoin(std::vector<int>&, std::vector<int>&, unsigned);
    void updateJoin(std::vector<int>&, std::vector<int>&, unsigned);
    void insertUninit(const llvm::Instruction *, NodeIndex, std::set<NodeIndex> &); 
    //used for manually summaries functions 
    void processInitFuncs(llvm::Instruction *, llvm::Function *, bool, std::vector<int>&, std::vector<int>&);
    void processCopyFuncs(llvm::Instruction *, llvm::Function *, bool, std::vector<int>&, std::vector<int>&);
    void processTransferFuncs(llvm::Instruction *, llvm::Function *, bool, std::vector<int>&, std::vector<int>&);
    void processFuncs(llvm::Instruction *, llvm::Function *, bool, std::vector<int>&, std::vector<int>&);

    //used for requirement propagation
    void backPropagateReq(llvm::Instruction*, llvm::Value*, std::vector<int>&);  
    void setReqFor(const llvm::Instruction *, const llvm::Value *, std::vector<int>&, std::set<const llvm::Value*>&);
    void DFS(llvm::Instruction *, NodeIndex);
    void summarizeFuncs(llvm::ReturnInst*);
    void propInitFuncs(llvm::Instruction *, int*);
    void propCopyFuncs(llvm::Instruction *, int*);
    void propTransferFuncs(llvm::Instruction *, int*);
    void propFuncs(llvm::Instruction *, llvm::Function *, int*);
    //used for function checking.
    void checkCopyFuncs(llvm::Instruction *, llvm::Function *);
    void checkTransferFuncs(llvm::Instruction *, llvm::Function *);
    void checkFuncs(llvm::Instruction *, llvm::Function *);
    bool warningReported(llvm::Instruction*, NodeIndex idx); 
    enum WarnType getFieldTy(llvm::Type *, int);
    enum WarnType getWType(llvm::Type *);

    void initSummary();
public:
    
    FuncAnalysis(llvm::Function *F_, GlobalContext *Ctx_, bool flag)
            : F(F_), Ctx(Ctx_) {
        M = F->getParent();
        DL = &(M->getDataLayout());
        printWarning = flag;
	    nodeFactory.setModule(M);
        nodeFactory.setDataLayout(DL);
        nodeFactory.setGlobalContext(Ctx_);
        nodeFactory.setStructAnalyzer(&(Ctx->structAnalyzer));
        nodeFactory.setGobjMap(&(Ctx->Gobjs));
        VisitIns.clear();
	    warningSet.clear();
    }
    bool run(bool flag);
};
class Tarjan {
private:
    std::unordered_map<llvm::Function*, std::set<llvm::Function*>> depCG;
    std::unordered_set<llvm::Function *> funcs;

    std::unordered_set<llvm::Function *> depVisit;
    std::stack<llvm::Function *> Stack;
    std::unordered_map<llvm::Function*, int> dfn;
    std::unordered_map<llvm::Function*, int> low;
    std::unordered_map<llvm::Function*, bool> inStack;
    std::vector<llvm::Function*> sc;
    std::vector<std::vector<llvm::Function*>> SCC;
    int ts = 1;
    int ind = 0;
    int sccSize = 0;
    int rec = 0;

    int biggest = 0;
public:
    Tarjan(std::unordered_map<llvm::Function*, std::set<llvm::Function*>> _depCG) {
        depCG = _depCG;
        for (auto item : _depCG) {
            funcs.insert(item.first);
            for (auto callee : item.second) {
                funcs.insert(callee);
            }
        }
        depVisit.clear();
    };
    void getSCC(std::vector<std::vector<llvm::Function*>> &);
    void dfs(llvm::Function *F);
};
int64_t getGEPInstFieldNum(const llvm::GetElementPtrInst* gepInst,
    const llvm::DataLayout* dataLayout, const StructAnalyzer& structAnalyzer, llvm::Module* module);

#endif //PROJECT_QUALIFIERANALYSIS_H
