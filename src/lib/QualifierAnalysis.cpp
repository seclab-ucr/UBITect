//
// Created by ubuntu on 2/8/18.
//

#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/IR/CFG.h>

#include <queue>
#include <deque>
#include <cstring>
#include <set>
#include <stack>

#include "Annotation.h"
#include "QualifierAnalysis.h"
#include "FunctionSummary.h"
#include "CallGraph.h"
#include "Helper.h"

//#define SERIALIZATION
//#define LOADSUM
#define RUN_ON_FUNC
//#define _PRINT_NODEFACTORY
//#define _PRINT_INST
//#define DEBUG_TITLE
//#define _PRINT_SUMMARY
//#define _PRINT_SUMNODEFACT
//#define _PRINT_PTS
//#define IN
//#define OUT
//#define gep_check
// #define _INIT_NF
//#define _DBG
#define _FIND_DEP
//#define  _PRINT_SCC
//#define PRINT_BIGCIRCLE
//#define CAL_BIGCIRCLE
//#define COLLECT
#define CAL_STACKVAR
using namespace llvm;

std::string testDir = getCurrentWorkingDir() + "/Summary/";

static bool isCastingCompatibleType(Type *T1, Type *T2);
bool QualifierAnalysis::doInitialization(llvm::Module *M) {
    //set name for each BB
    // collect global object definitions
    for (GlobalVariable &G : M->globals()) {
        if (G.hasExternalLinkage())
            Ctx->Gobjs[G.getName().str()] = &G;
    }
#ifdef HEAP_CHECK
        //To filter the heap warning, we need to record every use of the struct.
    const llvm::DataLayout *DL = &(M->getDataLayout());
    for (Module::iterator fi = M->begin(), fe = M->end(); fi != fe; ++fi)
    {
        Function *F = &*fi;
        if (F->isIntrinsic())
            continue;
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)
        {
            if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(&*i))
            {
                const Type *type = cast<PointerType>(GEPI->getOperand(0)->getType())->getElementType();
                // An array is considered a single variable of its type.
                while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
                    type = arrayType->getElementType();
                if (const StructType *structType = dyn_cast<StructType>(type))
                {
                    if (!structType->isOpaque() && !structType->isLiteral())
                    {
                        int64_t offset = getGEPOffset(GEPI, DL);
                        int fieldNum = offsetToFieldNum(GEPI->getOperand(0)->stripPointerCasts(), offset, DL,
                        &Ctx->structAnalyzer, M);
                        for (User *U : GEPI->users())
                        {
                            if (Instruction *Use = dyn_cast<Instruction>(U))
                            {
                                if (isa<LoadInst>(Use) || isa<GetElementPtrInst>(Use)||isa<StoreInst>(Use))
                                {
                                    Ctx->usedField[structType].insert(fieldNum);
                                }
                            }
                        }
                    }  
                }
            }
        }
    }
#endif
    return false;
}

bool QualifierAnalysis::doModulePass(llvm::Module * M){
    module = M;
    DL = &(M->getDataLayout());
    bool ret = false;

    for (Module::iterator f = M->begin(), fe = M->end(); f != fe; ++f) {
        Function *F = &*f;

#ifdef READYLIST_DEBUG
        OP << "Ready List:\n";
        for (auto rf: Ctx->ReadyList) {
            OP << rf->getName().str() << "\n";
        }
#endif

        if (Ctx->ReadyList.find(F) != Ctx->ReadyList.end() && (!Ctx->Visit[F])) {
	    #ifdef RUN_ON_FUNC
            runOnFunction(F, true);
	    #endif
            FCounter++;
            Ctx->Visit[F] = true;
            for (Function *caller : Ctx->CalledMaps[F]) {
                Ctx->RemainedFunction[caller]--;
                if (Ctx->RemainedFunction[caller] == 0) {
                    Ctx->ReadyList.insert(caller);
                }
            }
            ret = true;
        }
    }
    return ret;
}
void DFSUntil(std::map<llvm::Function*, std::set<llvm::Function*>> &CM, llvm::Function* F, std::set<llvm::Function*> &depVisit, std::vector<llvm::Function*> &sc) {
	sc.push_back(F);
	depVisit.insert(F);
	for (auto i : CM[F]) {
		if (depVisit.find(i) == depVisit.end()) 
			DFSUntil(CM, i, depVisit, sc);
	}
}

std::map<llvm::Function*, std::set<llvm::Function*>> getTranspose(std::map<llvm::Function*, std::set<llvm::Function*>> &CG) {
	std::map<llvm::Function*, std::set<llvm::Function*>> CM;
	for (std::map<llvm::Function*, std::set<llvm::Function*>>::iterator i = CG.begin(); i != CG.end(); i++) {
		for (auto item : i->second)
			CM[item].insert(i->first);
	}
	return CM;
}
void fillOrder(std::map<llvm::Function*, std::set<llvm::Function*>> &depCG,llvm::Function* F, std::set<llvm::Function*> &depVisit, std::stack<llvm::Function*> &Stack) {
	depVisit.insert(F);
	if (depCG[F].size() != 0) {
		for (auto item : depCG[F]) {
			if (depVisit.find(item) == depVisit.end()) {
				fillOrder(depCG, item, depVisit, Stack);
			}
		}
	}

	Stack.push(F);
}

void QualifierAnalysis::collectRemaining() {
    //For functions that does not visited, find the path 
    #ifdef _FIND_DEP
        int count = 0;
	//The new graph we need to calculate0
	std::map<llvm::Function*, std::set<llvm::Function*>> depCG;
        for (auto i : Ctx->CallMaps) {
                if (Ctx->Visit.find(i.first) != Ctx->Visit.end() && (!Ctx->Visit[i.first])) {
               		count++;
		} 
		for (auto item : i.second) {
			if (Ctx->Visit.find(item) != Ctx->Visit.end() && (!Ctx->Visit[item])) {
				depCG[i.first].insert(item);
			}
		}
        }
	#ifdef _PRINT_DEPCG
        OP<<count<<" Functions are enrolled with dependecies.\n";
	
	OP<<"dep CG whose size is "<<depCG.size()<<"\n";
	for (auto item : depCG) {
		OP<<item.first->getName().str()<<" dep calls: ";
		for (auto i: item.second) {
			OP<<i->getName().str()<<"/";
		}
		OP<<"\n";
	}
	#endif
        std::set<llvm::Function *> depVisit;
	std::stack<llvm::Function *> Stack;

        for (auto i : depCG) {
                if (depVisit.find(i.first) != depVisit.end())
                        continue;
		/*
                if (i.second.find(i.first) != i.second.end()){
                        OP<<"target circle path: \n";
                        OP<<i.first->getName().str()<<"->"<<i.first->getName().str()<<"\n";
                        depVisit.insert(i.first);
                        continue;
                }*/
		fillOrder(depCG, i.first, depVisit, Stack);
        }

	std::map<llvm::Function*, std::set<llvm::Function*>> CM = getTranspose(depCG);
	depVisit.clear();

	int sccCount = 0;	
	int numRec = 0;
	int numInd = 0;
	std::vector<llvm::Function*> bigCircle;
	//SCC records the functions within loop
	while (!Stack.empty()) {
		llvm::Function *v = Stack.top();
		Stack.pop();
		std::vector<llvm::Function*> sc;
		sc.clear();
		if (depVisit.find(v) == depVisit.end()) {
			sccCount++;
			DFSUntil(CM, v, depVisit, sc);
		}
		if (sc.size() == 1) {
			if (depCG[sc.at(0)].find(sc.at(0)) != depCG[sc.at(0)].end()) {
				numRec++;
				Ctx->rec.insert(sc.at(0));
			}
			else
 				numInd++;
		}
		if (sc.size() > 1)
			Ctx->SCC.push_back(sc);
	}
	#ifdef _PRINT_SCC
	OP<<"SCC size(>1) = "<<Ctx->SCC.size()<<"\n";
	OP<<numRec<<" recursive functions.\n";
	OP<<numInd<<" ind functions.\n";
	OP<<"recursive functions: \n";
	for (auto item : Ctx->rec) {
		OP<<item->getName().str()<<" in module "<<item->getParent()->getName().str()<<"\n";
	}
	OP<<"print each SCC:\n";
	for (auto item : Ctx->SCC) {
		OP<<"scc size : "<<item.size()<<"\n";
		for (auto it : item) {
			OP<<it->getName().str()<<"/";
		}
		OP<<"\n";
		if (item.size() > 100)
			bigCircle = item;
	}
	#endif
	int noVisit = 0;
	for(auto i : Ctx->Visit){
	    if(!i.second) {
		Ctx->ChangeMap[i.first] = true;	
		noVisit++;
	    }
	}
	//calculate the summary for functions in SCC and add them to the ready listi
	calSumForRec(Ctx->rec);
	calSumForScc(Ctx->SCC);
	#endif
	//Now we get the big circle, build the depCG for the element in big circle, get the indirect call for it.
	//std::map<llvm::Function*, std::set<llvm::Function*>> circleCG;
	#ifdef PRINT_BIGCIRCLE
	OP<<"Indirect call of the big loop : \n";
	int direct = 0;
	int indirect = 0;
	llvm::Function* popCaller;
	llvm::Function* popCallee;
	int popCallerCount=0;
	std::map<llvm::Function*, int> calleeTimes;

	
	for (auto item : bigCircle) {
		int localInd = 0;
	    for (auto callee : depCG[item]) {
		std::vector<llvm::Function*>::iterator iter = std::find(bigCircle.begin(), bigCircle.end(), callee);
		if (iter != bigCircle.end()) {
		    if (Ctx->DirectCallMap[item].find(callee) != Ctx->DirectCallMap[item].end()) {
			direct++;
		    }
		    else {
			//indirect call
			indirect++;
			localInd ++;
			OP<<item->getName().str()<<" --> "<<callee->getName().str()<<"\n";

			if (calleeTimes.find(callee) != calleeTimes.end())
			    calleeTimes[callee]++;
			else
			    calleeTimes[callee] = 1;
		    }
		}
	    }
	    if (localInd > popCallerCount) {
		popCaller = item;
		popCallerCount = localInd;
	    }
	}
	OP<<direct<<" direct calls in big Circle while "<<indirect<<" indirect calls in big circle.\n";
	OP<<"The most popular caller is: "<<popCaller->getName().str()<<": "<<popCallerCount<<" times.\n";
	int popCalleeCount = 0;
	for (auto item: calleeTimes){
		if (item.second > popCalleeCount) {
			popCalleeCount = item.second;
			popCallee = item.first;
		}
	}
	OP<<"The most popular callee is: "<<popCallee->getName().str()<<": "<<popCalleeCount<<" times.\n";
	#endif
	#ifdef CAL_BIGCIRCLE
	OP<<"recursively calculate the big Circle:\n";
	int readyCount = 0;
	std::queue<llvm::Function*> scQueue;
        for (auto item : bigCircle) {
            scQueue.push(item);
        }	
	while (!scQueue.empty()) {
                llvm::Function *func = scQueue.front();
                scQueue.pop();
                
		Summary in;
                std::string fname = getScopeName(func);
                if(Ctx->FSummaries.find(func) != Ctx->FSummaries.end()) {
                        in.copySummary(in, Ctx->FSummaries[func], func);
                }
                runOnFunction(func, false);
                if(Ctx->FSummaries[func].equal(in))
                {
                        readyCount++;
                        Ctx->ChangeMap[func] = false;
                        Ctx->ReadyList.insert(func);
                        for (Function *caller : Ctx->CalledMaps[func]) {
                            Ctx->RemainedFunction[caller]--;
                            if (Ctx->RemainedFunction[caller] == 0) {
                                 Ctx->ReadyList.insert(caller);
                            }
                        }
                }
                else{
                        scQueue.push(func);
                        Ctx->ChangeMap[func] = true;
                }
            }	

#endif
}
void QualifierAnalysis::calDepFuncs() {
}
bool QualifierAnalysis::doFinalization(llvm::Module *M) {
    module = M;
    DL = &(M->getDataLayout());
    bool ret = false;

    for (Module::iterator f = M->begin(), fe = M->end(); f != fe; ++f) {
        Function *F = &*f;

        if (Ctx->ReadyList.find(F) != Ctx->ReadyList.end() && (!Ctx->Visit[F])) {
            OP<<"runOnFunction"<<F->getName().str()<<"\n";
            #ifdef RUN_ON_FUNC
            runOnFunction(F, true);
            #endif
            FCounter++;
            OP << FCounter << " Function Finished!\n";
            Ctx->Visit[F] = true;
            for (Function *caller : Ctx->CalledMaps[F]) {
                Ctx->RemainedFunction[caller]--;
                if (Ctx->RemainedFunction[caller] == 0) {
                    Ctx->ReadyList.insert(caller);
                }
            }
            ret = true;
        }
    }
    return ret;
}

void QualifierAnalysis::finalize() {
}

bool QualifierAnalysis::runOnFunction(llvm::Function *f, bool flag) {
    FuncAnalysis FA(f, Ctx);
    FA.run(flag);
    return false;
}

bool FuncAnalysis::run(bool flag) {
    buildPtsGraph();
    initSummary();
    computeAASet();
    NodeIndex numNodes = nodeFactory.getNumNodes();
    qualiInference();
    #ifdef CAL_STACKVAR
    calStackVar();
    #endif
    fSummary.copySummary(Ctx->FSummaries[F], fSummary, F);
    std::string FScopeName = getScopeName(F);
    if(flag){
	QualifierCheck();
	Ctx->uninitArg += getUninitArg();
	Ctx->uninitOutArg += getUninitOutArg();
	//update = -1
	Ctx->ignoreOutArg += getIgnoreOutArg();
    }
    return false;
}

void FuncAnalysis::buildPtsGraph() {
    PtsGraph initPtsGraph;
    createInitNodes(initPtsGraph);

    for(Function::iterator bb = F->begin(); bb != F->end(); ++bb)
        for(BasicBlock::iterator itr = bb->begin(); itr != bb->end(); itr++)
        {
            NodeIndex idx = nodeFactory.createValueNode(&*itr);
        }
    std::deque<BasicBlock*> worklist;
    for(Function::iterator bb = F->begin(), be = F->end(); bb != be; ++bb) {
        worklist.push_back(&*bb);
    }

    Instruction *entry = &(F->front().front());
    NodeIndex entryIndex = nodeFactory.getValueNodeFor(entry);
    unsigned count = 0;
    unsigned threshold = 20 * worklist.size();

    while (!worklist.empty() && ++count <= threshold) {
        BasicBlock *BB = worklist.front();
        worklist.pop_front();

        PtsGraph in;
        PtsGraph out;

        // calculates BB in
        if (BB == &F->front()) {
            in = initPtsGraph;
        } else {
            for (auto pi = pred_begin(BB), pe = pred_end(BB); pi != pe; ++pi) {
                const BasicBlock *pred = *pi;
                const Instruction *b = &pred->back();
                unionPtsGraph(in, nPtsGraph[b]);
            }
        }

        bool changed = false;
        for (BasicBlock::iterator ii = BB->begin(), ie = BB->end(); ii != ie; ++ii) {
            Instruction *I = &*ii;
            if (I != &BB->front())
                in = nPtsGraph[I->getPrevNode()];
            
            out = processInstruction(I, in);
            if (I == &BB->back()) {
                PtsGraph old = nPtsGraph[I];
                if (out != old)
                    changed = true;
            }
            nPtsGraph[I] = out;

        }

        if (changed) {
            for (auto si = succ_begin(BB), se = succ_end(BB); si != se; ++si) {
                BasicBlock *succ = *si;
                if (std::find(worklist.begin(), worklist.end(), succ) == worklist.end())
                    worklist.push_back(succ);
            }
        }
    } //worklist
}
void FuncAnalysis::handleGEPConstant(const ConstantExpr *ce, PtsGraph &in)
{
	NodeIndex gepIndex = nodeFactory.getValueNodeFor(ce);
                NodeIndex srcNode = nodeFactory.getValueNodeFor(ce->getOperand(0));
                int64_t offset = getGEPOffset(ce, DL);
                int fieldNum = 0;
                if (offset < 0) {
                    // update the out pts graph instead of the in
                    //<= functon: acpi_ns_validate_handle: %7 = icmp eq i8* %6, getelementptr (i8, i8* null, i64 -1)
                    if (ce->getOperand(0)->isNullValue())
                        return;

                    //if(cast<PointerType>(ce->getType())->getElementType()->isIntegerTy(8))
                        //fieldNum = handleContainerOf(ce, offset, srcNode, in);
                    // XXX: negative encoded as unsigned
                } else {
                    fieldNum = offsetToFieldNum(ce->getOperand(0)->stripPointerCasts(), offset, DL,
                        &Ctx->structAnalyzer, M);
                }


                for (auto n : in[srcNode]) {
                    //assert(nodeFactory.isObjectNode(n) && "src ptr does not point to obj node");
                    //if (!nodeFactory.isObjectNode(n))
                    if (n > nodeFactory.getConstantIntNode() && !nodeFactory.isUnionObjectNode(n))
                        in[gepIndex].insert(n + fieldNum);
                    else
                        in[gepIndex].insert(n);
	}

}
PtsGraph FuncAnalysis::processInstruction(Instruction *I, PtsGraph &in) {

     // handle constant GEPExpr oprands here
    for (auto const &opr : I->operands()) {
        const Value *v = opr.get();
        if (const ConstantExpr* ce = dyn_cast<ConstantExpr>(v)) {
            if (ce->getOpcode() == Instruction::GetElementPtr) {
                NodeIndex gepIndex = nodeFactory.getValueNodeFor(ce);
                NodeIndex srcNode = nodeFactory.getValueNodeFor(ce->getOperand(0));
                int64_t offset = getGEPOffset(ce, DL);
                int fieldNum = 0;
                if (offset < 0) {
                    // update the out pts graph instead of the in
                    //<= functon: acpi_ns_validate_handle: %7 = icmp eq i8* %6, getelementptr (i8, i8* null, i64 -1)
                    if (ce->getOperand(0)->isNullValue())
                        continue;

                    if(I->getType()->isPointerTy() && cast<PointerType>(I->getType())->getElementType()->isIntegerTy(8))
                        fieldNum = handleContainerOf(I, offset, srcNode, in);
                    // XXX: negative encoded as unsigned
                } else {
                    fieldNum = offsetToFieldNum(ce->getOperand(0)->stripPointerCasts(), offset, DL,
                        &Ctx->structAnalyzer, M);
                }

                //in[gepIndex].insert(nodeFactory.getObjNodeForGEPExpr(gepIndex));

                for (auto n : in[srcNode]) {
                    //assert(nodeFactory.isObjectNode(n) && "src ptr does not point to obj node");
                    //if (!nodeFactory.isObjectNode(n))
                    if (n > nodeFactory.getConstantIntNode() && !nodeFactory.isUnionObjectNode(n))
                        in[gepIndex].insert(n + fieldNum);
                    else
                        in[gepIndex].insert(n);
                }
            }
	    if (ce->getOpcode() == Instruction::BitCast)
	    {
		if(const ConstantExpr* cep = dyn_cast<ConstantExpr>(ce->getOperand(0)))
		{
			if(cep->getOpcode() == Instruction::GetElementPtr)
			{
				handleGEPConstant(cep, in);		
			}
		}	
	    }
        }
    }

    PtsGraph out = in;
    switch (I -> getOpcode()) {
        case Instruction::Alloca: {
            NodeIndex valNode = nodeFactory.getValueNodeFor(I);
            assert (valNode != AndersNodeFactory::InvalidIndex && "Failed to find alloca value node");
            assert (I->getType()->isPointerTy());
            createNodeForPointerVal(I, I->getType(), valNode, out);
            //cannot call the function createNodeForPointer, because the allocated 
            break;
        }
        case Instruction::Load: {
            if (I->getType()->isPointerTy()) {
                // val = load from op
                NodeIndex ptrNode = nodeFactory.getValueNodeFor(I->getOperand(0));
                assert(ptrNode != AndersNodeFactory::InvalidIndex && "Failed to find load operand node");
                NodeIndex valNode = nodeFactory.getValueNodeFor(I);
                assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find load value node");
                
                for (auto i : in[ptrNode]) {
                    out[valNode].insert(in[i].begin(), in[i].end());
		    //if the ins is a pointer but it points to nothing, then we put universal ptr node into it.
		    if (out[valNode].isEmpty())
		    {
			out[valNode].insert(nodeFactory.getUniversalPtrNode());	
		    }
                }
            }
            break;
        } 
        case Instruction::Store: {
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I->getOperand(1));
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find store dst node");
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
            if (srcNode == AndersNodeFactory::InvalidIndex) {
                // If we hit the store insturction like below, it is
                // possible that the global variable (init_user_ns) is
                // an extern variable. Hope this does not happen,
                // otherwise we need to assume the worst case :-(

                // 1. store %struct.user_namespace* @init_user_ns,
                // %struct.user_namespace**  %from.addr.i, align 8
                // 2. @init_user_ns = external global %struct.user_namespace
                errs() << "Failed to find store src node for " << *I << "\n";
                break;
            }
            // assert(srcIndex != AndersNodeFactory::InvalidIndex && "Failed to find store src node");

            if (in.find(srcNode) != in.end()) {
                for (auto i : in[dstNode])
		{
			if (i <= nodeFactory.getConstantIntNode())
				continue;
			out[i] = in[srcNode];
			if (nodeFactory.isArgNode(srcNode)) {
				nodeFactory.setArgNode(i);
			}			
		}
            }
	    
            break;
        }
        case Instruction::GetElementPtr: {
            //dstNode = gep srcNode offset
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find gep src node");
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find gep dst node");
	    const GEPOperator* gepValue = dyn_cast<GEPOperator>(I);
    	    assert(gepValue != NULL && "getGEPOffset receives a non-gep value!");
            int64_t offset = getGEPOffset(I, DL);
	    llvm::Type *srcType = I->getType();
	    
	    const Type *type = cast<PointerType>(srcType)->getElementType();
    	    // An array is considered a single variable of its type.
    	    while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
        	type = arrayType->getElementType();

            //sequential gep inst, function pci_msi_prepare, we treat it as one field
            bool innerele = false;
            for (auto obj : in[srcNode])
            {
                if(offset < 0 && in[obj].getSize() == 1)
                {
                    for(auto inner : in[obj])
                    {
                        if(inner <= nodeFactory.getConstantIntNode() )
                            innerele = true;
                    }
                }
            }
            
            if(innerele)
            {
                out[dstNode] = in[srcNode];
                break;
            }
            int fieldNum = 0;
            bool onlyUnion = true;
            if (offset < 0) {
                bool special = true;
                for (auto obj : out[srcNode])
                {
                    if (obj <= nodeFactory.getConstantIntNode())
                    {
                        out[dstNode].insert(obj);
                        continue;
                    }
                    else{
                        special = false;
                    }
                    // update the out pts graph instead of the in
                }
                if(!special)
                {

                    if(cast<PointerType>(I->getType())->getElementType()->isIntegerTy(8))
                        fieldNum = handleContainerOf(I, offset, srcNode, out);
                }
                // XXX: negative encoded as unsigned
            }
            else {
                for (auto obj : out[srcNode])
                {
                    if (obj <= nodeFactory.getConstantIntNode())
                    {
                        out[dstNode].insert(obj);
                        continue;
                    } 
                    if (!nodeFactory.isUnionObjectNode(obj))
                    {
                        onlyUnion = false;
                    }
                }
                if(!onlyUnion)
                {
                    fieldNum = offsetToFieldNum(I->getOperand(0)->stripPointerCasts(), offset, DL,
                    &Ctx->structAnalyzer, M);
                }
                //check if the offset of union, but I remember I change the function offsetToFieldNum, 
                //so this could be removed? 

                for (auto n : in[srcNode]) {
                    #ifdef checkunion
                    if (nodeFactory.isUnionObjectNode(n))
                    {
                        out[dstNode].insert(n);
                        continue;
                    }
                    #endif
                    if (n > nodeFactory.getConstantIntNode())
                    {
                        if(fieldNum <= nodeFactory.getObjectSize(n))
                        {
                            unsigned bound = nodeFactory.getObjectBound(n);
                            if (n + fieldNum < bound)
                                out[dstNode].insert(n + fieldNum);
                            else 
                                out[dstNode].insert(n);
                        }
                        else    
                            out[dstNode].insert(nodeFactory.getUniversalPtrNode());
                    }
                    else
                        out[dstNode].insert(n);
                    
                }
            }
            // since we may have updated the pts graph, we need to use the out instead of in
                
            break;
        }
        case Instruction::PHI:{
            const PHINode* PHI = cast<PHINode>(I);
            if (PHI->getType()->isPointerTy()) {
                NodeIndex dstNode = nodeFactory.getValueNodeFor(PHI);
                assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find phi dst node");
                for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i) {
                    NodeIndex srcNode = nodeFactory.getValueNodeFor(PHI->getIncomingValue(i));
                    assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
                    if (in.find(srcNode) != in.end())
                        out[dstNode].insert(in[srcNode].begin(), in[srcNode].end());
                }
            }
            break;
        }
        case Instruction::BitCast: {
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find bitcast dst node");
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find bitcast src node");
            assert(I->getType()->isPointerTy());
            Type *T = cast<PointerType>(I->getType())->getElementType();
            Type *srcTy = cast<PointerType>(I->getOperand(0)->getType())->getElementType();
            //do not cast a union obj
            bool unionType = false;
            for(auto obj : out[srcNode])
            {
                if (obj <= nodeFactory.getConstantIntNode())
                    continue;
                unsigned objSize = nodeFactory.getObjectSize(obj);
                if (objSize == 1 && nodeFactory.isUnionObjectNode(obj))
                {
                    out[dstNode] = in[srcNode];
                    unionType = true;
                    break;
                }
            }
            if(unionType)
                break;
            if (StructType *srcST = dyn_cast<StructType>(srcTy))
            {
                if (!srcST->isLiteral() && srcST->getStructName().startswith("union"))
                {
                    out[dstNode] = in[srcNode];
                    break;
                }    
            }
            if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(I->getOperand(0)))
            {
                
                if(getGEPOffset(GEPI, DL) != 0)
                {
                    out[dstNode] = in[srcNode];
                    break;
                }
                
            }
            if (StructType *ST = dyn_cast<StructType>(T)) {
                if (ST->isOpaque())
                {
                    out[dstNode] = out[srcNode];
                    break;
                }
                const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(ST, M);
                assert(stInfo != NULL && "Failed to find stinfo");
		
                unsigned stSize = stInfo->getExpandedSize();
                //disable assertion: retrieve_io_and_region_from_bio
                //assert(!in[srcNode].isEmpty());
                for (NodeIndex obj : in[srcNode]) {
                    if (obj <= nodeFactory.getConstantIntNode())
                        continue;
                    //special case: gep and then cast, <=Function get_dx_countlimit
                    if (!nodeFactory.isObjectNode(obj))
                        continue;
                    unsigned objSize = nodeFactory.getObjectSize(obj);
                    if (stSize > objSize) {
#if 0
                        OP << "BitCast: " << *I << ":"
                           << " dst size " << stSize
                           << " larger than src size " << objSize << "\n";
#endif
                        NodeIndex newObj = extendObjectSize(obj, ST, out);
                        unsigned newOffset = nodeFactory.getObjectOffset(newObj);
			//if the object is pointed in the middle, then load will cause problems, we need an assertion to promise the 
			//object is not read.
			if (newObj == obj)
			{
				for (User *U : I->users())
				{
					if (Instruction *Use = dyn_cast<Instruction>(U))
					{
							
						if (isa<LoadInst>(Use))
						{
							OP<<"Use: "<<*Use<<"\n";
							OP<<"Warning: Casting struct get used.\n";
						}
						if (isa<GetElementPtrInst>(Use))
						{
							GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(Use);
							int64_t off = getGEPOffset(GEPI, DL);
							if(off == 0)
								continue;
							for (User *GEPU : Use->users())
							{
								if (Instruction *GepUse = dyn_cast<Instruction>(GEPU))
								{
									if (isa<LoadInst>(GepUse))
			                        {
            			                OP<<"Use: "<<*GepUse<<"\n";
							OP<<"Warning: Casting struct get used.\n";
                       				 }
								}
							}
						}
						
					}
				}
			}
                        if (newObj != obj && nodeFactory.isArgNode(obj))
                        {
                            for (unsigned i = 0; i < stSize; i++)
                            {
                                nodeFactory.setArgNode(newObj - newOffset + i);
                            }
                        }
                        if (newObj != obj && nodeFactory.isHeapNode(obj))
                        {
                            for (unsigned i = 0; i < stSize; i++)
                            {
                                nodeFactory.setHeapNode(newObj - newOffset + i);
                            }
                        }
                    }
                    //the obj could not be the first element of the obj
                    else{
                        unsigned newOffset = nodeFactory.getObjectOffset(obj);
                        for (unsigned i = 0; i < stSize; i++)
                        {
                            if (stInfo->isFieldUnion(i))
                                nodeFactory.setUnionObjNode(obj - newOffset + i);
                        }
                        if (nodeFactory.isHeapNode(obj))
                        {
                            for (unsigned i = 0; i < stSize; i++)
                            {
                                nodeFactory.setHeapNode(obj - newOffset + i);
                            }
                        }
                    }
                }
            }
            // since we may have updated the pts graph, we need to use the out instead of in
            out[dstNode] = out[srcNode];
            break;
        }
        case Instruction::Trunc: {
            if (I->getType()->isPointerTy()) {
                NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
                assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find trunc src node");
                NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
                assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find trunc dst node");
                if (in.find(srcNode) != in.end())
                    out[dstNode] = in[srcNode];
            }
            break;
        }
        case Instruction::IntToPtr: {
            // Get the node index for dst
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find inttoptr dst node");
            assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find inttoptr src node");

            // ptr to int to ptr
            if (in.find(srcNode) != in.end() && !in[srcNode].isEmpty())
                out[dstNode] = in[srcNode];
	    else
		out[dstNode].insert(nodeFactory.getUniversalPtrNode());
            break;
        }
        // FIXME point arithmetic through int
        case Instruction::PtrToInt: {
            // Get the node index for dst
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find inttoptr dst node");
            assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find inttoptr src node");

            out[dstNode] = in[srcNode];
            break;
        }
        //case Instruction::BinaryOps: {
        //    break;
        //}
        case Instruction::Select: {
            out = in;
            if (I->getType()->isPointerTy()) {
                NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
                assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find select dst node");

                NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(1));
                assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node 1");
                if (in.find(srcNode) != in.end())
                out[dstNode].insert(in[srcNode].begin(), in[srcNode].end());

                srcNode = nodeFactory.getValueNodeFor(I->getOperand(2));
                assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node 2");
                if (in.find(srcNode) != in.end())
                    out[dstNode].insert(in[srcNode].begin(), in[srcNode].end());

            }
            break;
        }
        case Instruction::VAArg:
        {
            if (I->getType()->isPointerTy()) {
                NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
                assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find va_arg dst node");
                NodeIndex vaNode = nodeFactory.getVarargNodeFor(I->getParent()->getParent());
                assert(vaNode != AndersNodeFactory::InvalidIndex && "Failed to find va_arg node");
                if (in.find(vaNode) != in.end())
                    out[dstNode] = in[vaNode];
            }
            break;
        }
        case Instruction::Call: {
            CallInst *CI = dyn_cast<CallInst>(I);
	    if (CI->getCalledFunction())
            {
		std::string CFN = CI->getCalledFunction()->getName().str();
            }
            if (I->getType()->isPointerTy()) {
                NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
                assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find call dst node");
                out[dstNode].clear();
                bool init = false;
		if (CI->getCalledFunction())
		{
			std::string CFN = getScopeName(CI->getCalledFunction());
		}
                    for (auto func : Ctx->Callees[CI])
                    {
                        StringRef fName = func->getName();
                        if (!init)
                        {
                            createNodeForPointerVal(I, I->getType(), dstNode, out);
                            init = true;
                        }
                        
                        if (Ctx->HeapAllocFuncs.count(fName.str()))
                        {
                            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
                            for (auto obj : out[dstNode])
                            {
                                if (obj <= nodeFactory.getConstantIntNode())
                                    continue;
                                unsigned objSize = nodeFactory.getObjectSize(obj);
                                for (unsigned i = 0; i < objSize; i++)
                                {
                                    nodeFactory.setHeapNode(obj + i);
                                }
                            }
                        }
			else if (Ctx->CopyFuncs.count(fName.str()))
                    	{
			    if(CI->getNumArgOperands() < 3)
        			break;
			    if(!CI->getArgOperand(0)->getType()->isPointerTy() || !CI->getArgOperand(1)->getType()->isPointerTy())
        			break;
                            NodeIndex dstIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(0));
                            NodeIndex srcIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(1));
                            if (CI->getArgOperand(0)->getType()->isPointerTy() && CI->getArgOperand(1)->getType()->isPointerTy())
                            {
                                for (auto srcObj : out[srcIndex])
                                {
                                    for (auto dstObj : out[dstIndex])
                                    {
                                        out[dstObj].insert(out[srcObj].begin(), out[srcObj].end());
                                    }
                                }
                            }
                        }
                    }
            }
            break;
        }
        case Instruction::Ret: {
            if (I->getNumOperands() != 0) {
                Value *RV = I->getOperand(0);
                NodeIndex valNode = nodeFactory.getValueNodeFor(RV);
                assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find call return value node");
                if (RV->getType()->isPointerTy()) {
                    NodeIndex retNode = nodeFactory.getReturnNodeFor(F);
                    assert(retNode != AndersNodeFactory::InvalidIndex && "Failed to find call return node");
                    out[retNode] = in[valNode];
                } else {
                    if (!isa<ConstantInt>(RV)) {
                        auto itr = in.find(valNode);
                    }
                }
            }
            break;
        }
        default: {
            if (I->getType()->isPointerTy())
                OP << "pointer-related inst not handled!" << *I << "\n";
            out = in;
            break;
        }
    } //switch(I->getOpCode())
    return out;
}

void FuncAnalysis::unionPtsGraph(PtsGraph &pg, const PtsGraph &other)
{
    for (auto itr2 = other.begin(), end2 = other.end(); itr2 != end2; ++itr2) {
        auto itr1 = pg.find(itr2->first);
        if (itr1 != pg.end())
            itr1->second.insert(itr2->second.begin(), itr2->second.end());
        else
            pg.insert(std::make_pair(itr2->first, itr2->second));
    }
}

void FuncAnalysis::initSummary()
{
    fSummary.relatedBC.insert(F->getParent()->getName().str());
    //retValue and argValue node are created in: createInitNodes
    Instruction *beginIns = &(F->front().front());
    Instruction *endIns = &(F->back().back());
    //1-1. create return value node and argument value node
    NodeIndex sumRetNode = fSummary.sumNodeFactory.getValueNodeFor(F);
    NodeIndex retNode = nodeFactory.getReturnNodeFor(F);
    //1-2 create return object node
    if (F->getReturnType()->isVoidTy())
    {
        fSummary.sumPtsGraph[sumRetNode].clear();
    }
    else
    {
        //create node and build the pts relations of return object
        for (auto obj : nPtsGraph[endIns][retNode])
        {
            if (obj <= nodeFactory.getConstantIntNode())
                continue;
            unsigned objSize = nodeFactory.getObjectSize(obj);
            if(fSummary.sumNodeFactory.getObjectNodeFor(F) != AndersNodeFactory::InvalidIndex)
                break;
	    fSummary.setRetSize(objSize);
            NodeIndex sumRetObjNode = fSummary.sumNodeFactory.createObjectNode(F);
            if (nodeFactory.getObjectOffset(obj) == 0)
            {
                fSummary.sumPtsGraph[sumRetNode].insert(sumRetObjNode);
		fSummary.setRetOffset(0);
	    }
            for(unsigned i = 1; i< objSize; i++)
            {
                NodeIndex sumObjNode = fSummary.sumNodeFactory.createObjectNode(sumRetObjNode, i);
                if (i == nodeFactory.getObjectOffset(obj))
                {
                    fSummary.sumPtsGraph[sumRetNode].insert(sumObjNode);
		    fSummary.setRetOffset(i);
                }
            }
        }
    }
    //1-3 create argument object node
    int argNo = 0;
    for (auto const &a : F->args())
    {
        const Argument *arg = &a;
        NodeIndex argNode = nodeFactory.getValueNodeFor(arg);
        NodeIndex sumArgNode = fSummary.sumNodeFactory.getValueNodeFor(arg);
	
	fSummary.args[sumArgNode].setNodeIndex(sumArgNode);
	fSummary.args[sumArgNode].setNodeArgNo(argNo);
        //create node for object, set the sumPts information
        //create the array for update and requirement of the function
        for (auto obj : nPtsGraph[endIns][argNode])
        {
            if (obj <= nodeFactory.getConstantIntNode())
                continue;
            unsigned objSize = nodeFactory.getObjectSize(obj);
	    NodeIndex sumArgObjNode = fSummary.sumNodeFactory.getObjectNodeFor(arg);
            if(sumArgObjNode != AndersNodeFactory::InvalidIndex)
                break;
	    fSummary.args[argNo].setObjSize(objSize);
            sumArgObjNode = fSummary.sumNodeFactory.createObjectNode(arg);
            if(nodeFactory.getObjectOffset(obj) == 0)
	    {
                fSummary.sumPtsGraph[sumArgNode].insert(sumArgObjNode);
		fSummary.args[sumArgObjNode].setNodeArgNo(argNo);
		fSummary.args[sumArgObjNode].setOffset(0);
	    }
            for(unsigned i = 1; i< objSize; i++)
            {
                NodeIndex objNode = fSummary.sumNodeFactory.createObjectNode(sumArgObjNode, i);
		fSummary.args[objNode].setNodeArgNo(argNo);
		if (i == nodeFactory.getObjectOffset(obj))
                {
                    fSummary.sumPtsGraph[sumArgNode].insert(objNode);
		    fSummary.args[argNo].setOffset(i);
                }
            }
        }
		argNo++;
    }
    //2. create the summary array for both update and requirments
    unsigned numNodes = fSummary.sumNodeFactory.getNumNodes();
    fSummary.noNodes = numNodes;
    fSummary.reqVec.resize(numNodes); //= new int[numNodes];
    fSummary.updateVec.resize(numNodes); //= new int[numNodes];
    fSummary.changeVec.resize(numNodes);
    for(unsigned i = 0; i<numNodes; i++)
    {
        fSummary.reqVec.at(i) = _UNKNOWN;
        fSummary.updateVec.at(i) = _UNKNOWN;
	fSummary.changeVec.at(i) = _UNKNOWN;
    }
}
// given old object node and new struct info, extend the object size
// return the new object node
NodeIndex FuncAnalysis::extendObjectSize(NodeIndex oldObj, const StructType* stType, PtsGraph &ptsGraph) {
    // FIXME: assuming oldObj is the base <= function: acpi_dev_filter_resource_type
    //disable assertion:  function: acpi_dev_filter_resource_type
    //assert(nodeFactory.getObjectOffset(oldObj) == 0);
    if(nodeFactory.getObjectOffset(oldObj) != 0)
        return oldObj;

    const Value *val = nodeFactory.getValueForNode(oldObj);
    assert(val != nullptr && "Failed to find value of node");
    NodeIndex valNode = nodeFactory.getValueNodeFor(val);

    // before creating new obj, remove the old ptr->obj
    auto itr = ptsGraph.find(valNode);
    //function tcp_prune_ofo_queue
    assert(itr != ptsGraph.end());
    if(!itr->second.has(oldObj))
    {
        OP<<"valNode does not own the oldObj.";
    }
    itr->second.reset(oldObj);
    nodeFactory.removeNodeForObject(val);

    // create new obj
    NodeIndex newObj = processStruct(val, stType, valNode, ptsGraph);
    //set ArgNode:
    if(nodeFactory.isArgNode(oldObj))
    {
        unsigned stSize = nodeFactory.getObjectSize(newObj);
        unsigned newOffset = nodeFactory.getObjectOffset(newObj);
        for(unsigned i = 0; i < stSize; i++)
            nodeFactory.setArgNode(newObj - newOffset + i);
    }
    // update ptr2set. all the pointers to oldObj should to new Obj
    updateObjectNode(oldObj, newObj, ptsGraph);

    return newObj;
}

// given the old object node, old size, and the new object node
// replace all point-to info to the new node
// including the value to object node mapping
void FuncAnalysis::updateObjectNode(NodeIndex oldObj, NodeIndex newObj, PtsGraph &ptsGraph) {
    unsigned offset = nodeFactory.getObjectOffset(oldObj);
    NodeIndex baseObj = nodeFactory.getOffsetObjectNode(oldObj, -(int)offset);
    unsigned size = nodeFactory.getObjectSize(oldObj);
    // well, really expensive op
    // use explicit iterator for updating
    for (auto itr = ptsGraph.begin(), end = ptsGraph.end(); itr != end; ++itr) {
        AndersPtsSet temp = itr->second;
        // in case modification will break iteration
        for (NodeIndex obj : temp) {
            //if(nodeFactory.getOffset(obj) == 0)
                //continue;
            if (obj >= baseObj && obj < (baseObj + size)) {
                itr->second.reset(obj);
                itr->second.insert(newObj + (obj - baseObj));
            }
        }
    }
}

int FuncAnalysis::handleContainerOf(const Instruction* I, int64_t offset, NodeIndex srcNode, PtsGraph &ptsGraph) {
    assert(I->getType()->isPointerTy() && "passing non-pointer type to handleContainerOf");
    assert(cast<PointerType>(I->getType())->getElementType()->isIntegerTy(8) && "handleContainerOf can only handle i8*");
    assert(offset < 0 && "handleContainerOf can only handle negative offset");
    NodeIndex gepIndex = nodeFactory.getValueNodeFor(I);
    // for each obj the pointer can point-to
    // hopefully there'll only be one obj <= too young too naive, function: drm_vma_offset_lookup_locked, store nullptr or arg to it.
    //assert(ptsGraph[srcNode].getSize() == 1);
    for (NodeIndex obj : ptsGraph[srcNode]) {
        // if src obj special, ptr arithmetic is meaningless
        if (obj <= nodeFactory.getConstantIntNode())
            return 0;

        // find the allocated type
        const Value *allocObj = nodeFactory.getValueForNode(obj);
        const Type *allocType = allocObj->getType();

        // 1. check if allocated type is okay
        assert(allocType->isPointerTy());
        const StructType *stType = dyn_cast<StructType>(cast<PointerType>(allocType)->getElementType());
        if(!stType)
        {
            OP<<"!stType, the precise cannot be promised.\n";
            return 0;
        }
        //assert(stType && "handleContainerOf can only handle struct type");
        const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(stType, M);
        assert(stInfo != NULL && "structInfoMap should have info for st!");
        // find the size offset of src ptr
        // int64_t should be large enough for unsigned
        //srcField: the obj field from the current obj
        int64_t srcField = nodeFactory.getObjectOffset(obj);
        //szieOffset: the offset from the current obj
	if (srcField >= stInfo->getExpandedSize())
		continue;
        int64_t sizeOffset = stInfo->getFieldOffset(srcField);
        // check if the size offset of src ptr is large enough to handle the negative offset
        if (sizeOffset + offset >= 0) {
            // FIXME: assume only one obj
            int64_t dstField = offsetToFieldNum(I->getOperand(0)->stripPointerCasts(), sizeOffset + offset,
                DL, &Ctx->structAnalyzer, M);
            //? src - dst?
            return (int)(dstField - srcField);
        }

        // 2. If the allocated type is not large enough to handle the offset,
        //    create a new one and update the ptr2set
        // get real type from later bitcast
        const Type *realType = nullptr;
        const Value *castInst = nullptr;
        for (auto U : I->users()) {
            if (isa<BitCastInst>(U)) {
                realType = U->getType();
                castInst = U;
                //break;
                //#ifdef nonsense
                //comment for function queue_attr_show in blk-sysfs, var %24.
                if (isa<GetElementPtrInst>(U->getOperand(0)))
                {
                    ptsGraph[gepIndex] = ptsGraph[srcNode]; 
                    OP<<"gep inst, the precise cannot be promised.\n";
                    return 0;
                }
                //#endif

            }
        }
        //assertion disabled: function dm_per_bio_data
        if (!realType)
        {
            OP<<"Failed to find the dst type for container_of\n";
            return 0;

        }
        //assert(realType && "Failed to find the dst type for container_of");
        assert(realType->isPointerTy());
        //special case: function dequeue_func
        const StructType *rstType = dyn_cast<StructType>(cast<PointerType>(realType)->getElementType());

        if (!rstType)
        {
            OP<<"handleContainerOf can only handle struct type\n";
            return 0;
        }
        //assert(rstType && "handleContainerOf can only handle struct type");
        //
        // this is the tricky part, we need to find the field number inside the larger struct
        const StructInfo *rstInfo = Ctx->structAnalyzer.getStructInfo(rstType, M);
        assert(rstInfo != nullptr && "structInfoMap should have info for rst!");
        
        //double check the container type?
        // FIXME: assuming one container_of at a time
        // fix stInfo if srcField is not 0
        bool found_container = false;
        std::set<Type*> elementTypes = stInfo->getElementType(srcField);
        for (Type *t : elementTypes) {
            if (StructType *est = dyn_cast<StructType>(t)) {
                
                const StructInfo *estInfo = Ctx->structAnalyzer.getStructInfo(est, M);
                assert(estInfo != nullptr && "structInfoMap should have info for est!");
                if (estInfo->getContainer(rstInfo->getRealType(), -offset)) {
                    found_container = true;
                    break;
                }
            }
        }
        if (!found_container)
        {
            OP<<"found_container fails, the precise cannot be promised.";
            return 0;
        }

        // okay, now we have find the correct container
        // create the new obj, using the castinst as base
        // This is an ugly hack, because we don't really have an original obj
        
        NodeIndex valNode = nodeFactory.getValueNodeFor(castInst);
        assert(valNode != AndersNodeFactory::InvalidIndex && "Failed to find castinst node");
        NodeIndex castObjNode = processStruct(castInst, rstType, valNode, ptsGraph);
        ptsGraph[gepIndex].insert(castObjNode);
        // next, update the ptr2set to the new object
        unsigned subField = offsetToFieldNum(castInst, -offset, DL, &Ctx->structAnalyzer, M);
        NodeIndex newObjNode = nodeFactory.getOffsetObjectNode(castObjNode, subField);
        updateObjectNode(obj, newObjNode, ptsGraph);

        if (nodeFactory.isArgNode(obj))
        {
            unsigned newSize = nodeFactory.getObjectSize(newObjNode);
            unsigned newOffset = nodeFactory.getObjectOffset(newObjNode);
            for (unsigned i = 0; i < newSize;  i++)
            {
                nodeFactory.setArgNode(newObjNode - newOffset + i);
            }
                
        }
        // update the value -> obj map
        nodeFactory.updateNodeForObject(allocObj, newObjNode);
        // finally, return the offset/fieldNum
        return -subField;
    } // end for all obj in ptr2set
    return 0;
}
void QualifierAnalysis::calSumForRec (std::set<llvm::Function*>& rec) {
	int readyCount = 0;
	for (auto item : rec) {
	    Function *func = item;
	    #ifdef RUN_ON_FUNC
	    while (Ctx->ChangeMap[func]) {
		
	    	Summary in;
	    	std::string fname = getScopeName(func);
           	if(Ctx->FSummaries.find(func) != Ctx->FSummaries.end()) {
                	in.copySummary(in, Ctx->FSummaries[func], func);
            	}

            	runOnFunction(func, false);
	    	if(Ctx->FSummaries[func].equal(in))
            	{
                	Ctx->ChangeMap[func] = false;
            		readyCount++;
		}
	    	else {
			Ctx->ChangeMap[func] = true;
	    	}	
	    }//while (Ctx->ChangeMap[func]) 
	    #endif
	    //update the ready list
	    Ctx->ReadyList.insert(func);
	    readyCount++;
	    for (Function *caller : Ctx->CalledMaps[func]) {
        	Ctx->RemainedFunction[caller]--;
            	if (Ctx->RemainedFunction[caller] == 0) {
            	    Ctx->ReadyList.insert(caller);
            	}
            }

	}
}
void QualifierAnalysis::calSumForScc (std::vector<std::vector<llvm::Function*>>& SCC) {
	int readyCount = 0;
	int totalscc = 0;
	for (auto sc : SCC) {
	    std::queue<llvm::Function*> scQueue;
	    for (auto item : sc) {
		scQueue.push(item);
	    }
	    totalscc += sc.size();
	    while (!scQueue.empty()) {
		llvm::Function *func = scQueue.front();
		scQueue.pop();
		Summary in;
                std::string fname = getScopeName(func);
                if(Ctx->FSummaries.find(func) != Ctx->FSummaries.end()) {
                        in.copySummary(in, Ctx->FSummaries[func], func);
                }
		runOnFunction(func, false);
		if(Ctx->FSummaries[func].equal(in))
            	{
			readyCount++;
                	Ctx->ChangeMap[func] = false;	
			Ctx->ReadyList.insert(func);	
			for (Function *caller : Ctx->CalledMaps[func]) {
             		    Ctx->RemainedFunction[caller]--;
               		    if (Ctx->RemainedFunction[caller] == 0) { 
                   		 Ctx->ReadyList.insert(caller);
                	    }
            		}
            	}
            	else{
			scQueue.push(func);
                	Ctx->ChangeMap[func] = true;
            	}
	    }//while (!scQueue.empty())
	    OP<<readyCount<<" scc done!\n"; 
	}//for (auto sc : SCC)
}

static bool isCastingCompatibleType(Type *T1, Type *T2) {
    if (T1->isPointerTy()) {
        if (!T2->isPointerTy())
            return false;

        Type *ElT1 = T1->getPointerElementType();
        Type *ElT2 = T2->getPointerElementType();
        // assume "void *" and "char *" are equivalent to any pointer type
        if (ElT1->isIntegerTy(8) /*|| ElT2->isIntegerTy(8)*/)
            return true;
        //if(ElT1->isStructTy())
            //return true;

        return isCastingCompatibleType(ElT1, ElT2);
    } else if (T1->isArrayTy()) {
        if (!T2->isArrayTy())
            return false;
        Type *ElT1 = T1->getArrayElementType();
        Type *ElT2 = T2->getArrayElementType();
        return isCastingCompatibleType(ElT1, ElT1);
    } else if (T1->isIntegerTy()) {
        // assume pointer can be cased to the address space size
        if (T2->isPointerTy() && T1->getIntegerBitWidth() == T2->getPointerAddressSpace())
            return true;

        // assume all integer type are compatible
        if (T2->isIntegerTy())
            return true;
        else
            return false;
    } else if (T1->isStructTy()) {
        return true;
    }else {
        errs() << "Unhandled Types:" << *T1 << " :: " << *T2 << "\n";
        return T1->getTypeID() == T2->getTypeID();
    }
}
