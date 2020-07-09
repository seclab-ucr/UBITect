#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Value.h"

#include "QualifierAnalysis.h"
#include "Annotation.h"
#include "Helper.h"
#include <cstring>
#include <deque>
#include <algorithm>
#include <vector>
#include <cassert>
#include <string>
#include <stack>
#include <utility>

#define max(a, b) ((a) > (b) ? (a) : (b))

#define DEBUG_TITLE
//#define _PRINT_INST
#define RET_LIST
#define ListProp
//#define _RELATED
//#define _PRINT_QUALI_ARRAY
//#define _PRINT_INIT_ARRAY
//#define _PRINT_FSUMMARY
//#define INOUT
//#define OUT
//#define load_check
//#define CALL_OBJ
//OUTQ: print out the important qualifier changes for each instruction
//#define OUTQ
using namespace llvm;
bool isEqual(std::vector<int> a1, std::vector<int> a2, unsigned);
int getQualiForConstant(const ConstantExpr *, AndersNodeFactory &, std::vector<int>);
//bug 1: the length of the argument could be 0, so, we need to check the FSummary.len each time we use relavent information
void FuncAnalysis::qualiInference()
{
//dbg information
#ifdef DEBUG_TITLE
    OP << "Inside qualifier inference:\n";
#endif

    //The length of the qualifier array, the total number of the nodes
    const unsigned numNodes = nodeFactory.getNumNodes();
    std::vector<int> initArray;

    qualiReq.resize(numNodes);
    initArray.resize(numNodes);
    //OP<<"numNodes = "<<numNodes<<"\n";
    VisitIns.clear();
    //set all the init qualifier of local variable as UNKNOWN,
    //because the merge may happen before the variable really appears in the program;
    //Ex:%11 = phi %1, %2, but %1 and %2 comes from different block let the %11 always be _UD;
    for (NodeIndex i = 0; i < numNodes; i++)
    {
        qualiReq.at(i) = _UNKNOWN;
        initArray.at(i) = _UNKNOWN;
    }

    Instruction *entry = &(F->front().front());
    NodeIndex entryIndex = nodeFactory.getValueNodeFor(entry);

    setGlobalQualies(initArray);

#ifdef _PRINT_INIT_ARRAY
    OP << "init array:\n";
    for (int i = 0; i < numNodes; i++)
    {
        OP << "node " << i << ", qualifier = " << initArray[i] << "\n";
    }
#endif

    std::deque<BasicBlock *> worklist;
    for (Function::iterator bb = F->begin(), be = F->end(); bb != be; ++bb)
    {
        BasicBlock *BB = &*bb;
        worklist.push_back(BB);
    }

    std::vector<int> old(numNodes, 0);
    std::vector<int> in(numNodes, 0);
    std::vector<int> out(numNodes, 0);

    unsigned threshold = 20 * worklist.size();
    unsigned count = 0,infcount=0,  inscount=0;
    ReturnInst *RI = NULL;
    //For BB that we did not see, we do consider the qualifier of them to join
    for (inst_iterator itr = inst_begin(*F), ite = inst_end(*F); itr != ite; ++itr)
    {
        //inscount++;
        auto inst = itr.getInstructionIterator();
        if (isa<ReturnInst>(&*inst))
        {
            RI = dyn_cast<ReturnInst>(&*inst);
        }

        nQualiArray[&*inst].resize(numNodes);
        nQualiArray[&*inst].assign(initArray.begin(), initArray.end());
        nQualiUpdate[&*inst].resize(numNodes);
        nQualiUpdate[&*inst].assign(qualiReq.begin(), qualiReq.end());
    }
    //OP<<"==stat: inscount = "<<inscount<<"\n";
    for (Function::iterator iter = F->begin(); iter != F->end(); iter++)
    {
        BasicBlock *BB = &*iter;
        inQualiArray[BB].resize(numNodes);
        outQualiArray[BB].resize(numNodes);
        for (unsigned i = 0; i < numNodes; i++)
        {
            inQualiArray[BB].at(i) = _UNKNOWN;
            outQualiArray[BB].at(i) = _UNKNOWN;
        }
    }

    while (!worklist.empty())
    {
        if (count++ > threshold)
        {
            OP << "Do not converge within threshold.\n";
            break;
        }

        BasicBlock *BB = worklist.front();
        worklist.pop_front();

        //keep the previous qualifier array
        in.assign(initArray.begin(), initArray.end());
        for (int i = 0; i < numNodes; i++)
            out.at(i) = 0;

        const Instruction *firstIns = &(BB->front());
        Instruction *lastInst = (Instruction *)BB->getTerminator();

        //if the basic block is not the first BB, we need to merge the data info
        if (!(BB == &F->front()))
        {
            bool init = false;
            //OP<<"BB : "<<BB->getName().str()<<"\n";
            for (auto pi = pred_begin(BB), pe = pred_end(BB); pi != pe; ++pi)
            {
                BasicBlock *pred = *pi;

                Instruction *src = &pred->back();
                if (VisitIns.find(src) != VisitIns.end())
                {
                    if (isTerminationBB(pred)) continue;
                    if (!init)
                    {
                        in.assign(nQualiArray[src].begin(), nQualiArray[src].end());
                        init = true;
                    }
                    else
                    {
                        qualiJoin(in, nQualiArray[src], numNodes);
                    }
                }
            }
            inQualiArray[BB].assign(in.begin(), in.end());
        }
        bool changed = false;
        for (BasicBlock::iterator ii = BB->begin(), ie = BB->end(); ii != ie; ++ii)
        {
            Instruction *I = &*ii;
#ifdef _PRINT_INST
            OP << *I << "\n";
#endif
            if (I != &BB->front())
            {
                in.assign(nQualiArray[I->getPrevNode()].begin(), nQualiArray[I->getPrevNode()].end());
            }
            //infcount++;
            //clock_t sTime, eTime;
            //sTime = clock();
            computeQualifier(I, in, out);
            //eTime = clock();
            //OP<<"time: "<<(double)(eTime - sTime) / CLOCKS_PER_SEC<<"\n";
            VisitIns.insert(I);
#ifdef OUT
            for (unsigned i = 0; i < numNodes; i++)
            {
                if (in[i] != out[i])
                    OP << "Node " << i << ": " << out[i] << "\n";
            }
#endif
            //if (numNodes > 835)
            //    OP << "out[835] = " << out[835] << "\n";
            //OP<<"numNodes = "<<nodeFactory.getNumNodes()<<"\n";
            if (I == &BB->back())
            {
                if (nQualiArray.find(I) != nQualiArray.end())
                {
                    if (!isEqual(out, nQualiArray[I], numNodes))
                        changed = true;
                }
                outQualiArray[BB].assign(out.begin(), out.end());
            }
            nQualiArray[I].assign(out.begin(), out.end());
            //OP<<"quali for constant: "<<nQualiArray[I][4]<<"\n";
        }
        ////OP<<"4\n";
        if (changed)
        {
            for (auto si = succ_begin(BB), se = succ_end(BB); si != se; ++si)
            {
                BasicBlock *succ = *si;
                if (std::find(worklist.begin(), worklist.end(), succ) == worklist.end())
                    worklist.push_back(succ);
            }
        }
    } //worklist.empty()
    //OP<<"==stat: infcount = "<<infcount<<"\n";
    Instruction *endIns = &(F->back().back());
    //summarize the return
    //OP<<"summarize the return:\n";
    bool init = false;
    //OP<<"numNodes = "<<nodeFactory.getNumNodes()<<", sumNumNodes = "<<fSummary.sumNodeFactory.getNumNodes()<<"\n";
    //NodeIndex sumRetNode = fSummary.sumNodeFactory.createValueNodeFor(F);
    if (!F->getReturnType()->isVoidTy() && RI)
    {
        //OP<<"qualifier at the end\n";
        std::set<const BasicBlock *> blacklist;
        std::set<const BasicBlock *> whitelist;
        std::set<NodeIndex> visit;

        NodeIndex retNode = nodeFactory.getValueNodeFor(RI->getReturnValue());
        NodeIndex sumRetNode = fSummary.sumNodeFactory.getValueNodeFor(F);
        fSummary.updateVec.at(sumRetNode) = nQualiArray[RI][retNode];

        //OP<<"retNode = "<<retNode<<", quali: "<<fSummary.updateVec.at(sumRetNode)<<"\n";
        //return value is related to arguments
        if (fSummary.updateVec.at(sumRetNode) == _UNKNOWN)
        {
            for (auto item : relatedNode[retNode])
            {
                //OP<<"item : "<<item<<", ";
                for (auto aa : nAAMap[RI][item])
                {
                    const llvm::Value *val = nodeFactory.getValueForNode(aa);
                    NodeIndex idx = AndersNodeFactory::InvalidIndex;
                    int offset = 0;
                    if (nodeFactory.isObjectNode(aa))
                    {
                        offset = nodeFactory.getObjectOffset(aa);
                        NodeIndex valIdx = fSummary.sumNodeFactory.getValueNodeFor(val);
                        if (valIdx == AndersNodeFactory::InvalidIndex)
                            continue;
                        for (auto obj : fSummary.sumPtsGraph[valIdx])
                        {
                            idx = obj;
                            break;
                        }
                    }
                    else
                    {
                        idx = fSummary.sumNodeFactory.getValueNodeFor(val);
                    }
                    //const llvm::Value *val = nodeFactory.getValueForNode(item);
                    //OP<<"Value : "<<*val<<", ";
                    //OP<<"idx = "<<idx<<", offset = "<<offset<<"\n";
                    if (idx != AndersNodeFactory::InvalidIndex)
                    {
                        //OP<<"idx + offset = "<<idx+offset<<"\n";
                        fSummary.args[sumRetNode].addToRelatedArg(idx + offset);
                    }
                }
            }
        }
        //If the return node might be uninitalized, then record the bl & wl
#ifdef RET_LIST
        if (fSummary.updateVec.at(sumRetNode) == _UD)
        {
            visit.clear();
            blacklist.clear();
            whitelist.clear();

            //OP << "calculate lists for sumRetNode:" << sumRetNode << ", retNode = "<<retNode<<": "<<nQualiArray[RI][retNode]<<"\n";
            calculateRelatedBB(retNode, RI, visit, blacklist, whitelist);
            //errs() << "whitelist:\n";
            for (auto witem : whitelist)
            {
                //errs() << witem->getName().str() << "\n";
                fSummary.args[sumRetNode].addToWhiteList(witem->getName().str());
            }
            //errs() << "\nblacklist:\n";
            for (auto bitem : blacklist)
            {
                //errs() << bitem->getName().str() << "\n";
                fSummary.args[sumRetNode].addToBlackList(bitem->getName().str());
            }
        }
#endif

        int qualiSrc = _UNKNOWN;
        //OP<<"retNode = "<<retNode<<"\n";
        //OP << "sumNodes:\n";
        //fSummary.summary();
        for (auto sumObj : fSummary.sumPtsGraph[sumRetNode])
        {
            //NodeIndex sumRetObjNode = fSummary.sumNodeFactory.getObjectNodeFor(F);
            unsigned sumObjOffset = fSummary.sumNodeFactory.getObjectOffset(sumObj);
            unsigned sumObjSize = fSummary.sumNodeFactory.getObjectSize(sumObj);
            //OP<<"sumObjOffset = "<<sumObjOffset<<", sumObj = "<<sumObj<<"sumObjSize="<<sumObjSize<<"\n";
            for (auto obj : nPtsGraph[RI][retNode])
            {
                //OP<<"obj = "<<obj<<"\n";

                if (!init)
                {
                    for (unsigned i = 0; i < sumObjSize; i++)
                    {
                        if (obj - sumObjOffset + i >= nodeFactory.getNumNodes())
                            break;
                        if (obj <= nodeFactory.getConstantIntNode())
                            qualiSrc = _ID;
                        else
                        {
                            qualiSrc = nQualiArray[endIns].at(obj - sumObjOffset + i);

                            if (qualiSrc == _UNKNOWN)
                            {
                                const llvm::Value *val = nodeFactory.getValueForNode(obj - sumObjOffset + i);
                                NodeIndex idx = fSummary.sumNodeFactory.getValueNodeFor(val);
                                if (idx != AndersNodeFactory::InvalidIndex)
                                {
                                    fSummary.args[obj - sumObjOffset + i].addToRelatedArg(idx);
                                }
                            }
                        }
                        fSummary.updateVec.at(sumObj - sumObjOffset + i) = qualiSrc;
                    }

                    init = true;
                }
                else
                {
                    for (unsigned i = 0; i < sumObjSize; i++)
                    {
                        //Tobe Fix: there should be a way to avoid this: function get_ringbuf
                        if (obj - sumObjOffset + i >= nodeFactory.getNumNodes())
                            break;
                        //OP<<"obj - sumObjOffset + i = "<<obj - sumObjOffset + i<<"\n";
                        if (obj <= nodeFactory.getConstantIntNode())
                            qualiSrc = _ID;
                        else
                        {
                            qualiSrc = nQualiArray[endIns].at(obj - sumObjOffset + i);

                            if (qualiSrc == _UNKNOWN)
                            {
                                const llvm::Value *val = nodeFactory.getValueForNode(obj - sumObjOffset + i);
                                NodeIndex idx = fSummary.sumNodeFactory.getValueNodeFor(val);
                                if (idx != AndersNodeFactory::InvalidIndex)
                                {
                                    fSummary.args[obj - sumObjOffset + i].addToRelatedArg(idx);
                                }
                            }
                        }
                        if (qualiSrc != _UNKNOWN)
                            fSummary.updateVec.at(sumObj - sumObjOffset + i) = std::min(fSummary.updateVec.at(sumObj - sumObjOffset + i), qualiSrc);
                    }
                }

#ifdef RET_LIST
                //OP<<"sumObjSize = "<<sumObjSize<<", numNodes = "<<numNodes<<"\n";
                //OP<<"sumObbjOffset = "<<sumObjOffset<<"\n";
                //OP<<"sumObj = "<<sumObj<<", obj = "<<obj<<"\n";
                for (unsigned i = 0; i < sumObjSize; i++)
                {
                    visit.clear();
                    blacklist.clear();
                    whitelist.clear();
                    if (obj < nodeFactory.getConstantIntNode()) {
                        continue;
                    }
                    if (nodeFactory.getObjectSize(obj) < sumObjSize)
                        continue;

                    //if (obj - sumObjOffset + i >= nodeFactory.getNumNodes())
                    //        break;
                    //OP<<"sumObj - sumObjOffset + i = "<<sumObj - sumObjOffset + i<<", obj - sumObjOffset+ i = "<<obj - sumObjOffset+ i<<"\n";
                    //OP<<"fSummary.updateVec.at("<<sumObj - sumObjOffset + i<<") = "<<fSummary.updateVec.at(sumObj - sumObjOffset + i)<<"\n";
                    if (fSummary.updateVec.at(sumObj - sumObjOffset + i) == _UD)
                    {
                        calculateRelatedBB(obj - sumObjOffset + i, RI, visit, blacklist, whitelist);
                        //errs()<<"whitelist:\n";
                        for (auto witem : whitelist)
                        {
                            //errs()<<witem->getName().str()<<"\n";
                            fSummary.args[sumObj - sumObjOffset + i].addToWhiteList(witem->getName().str());
                        }
                        //errs()<<"\nblacklist:\n";
                        for (auto bitem : blacklist)
                        {
                            //errs()<<bitem->getName().str()<<"\n";
                            fSummary.args[sumObj - sumObjOffset + i].addToBlackList(bitem->getName().str());
                        }
                    }
                }
#endif
            }
        }
    }

#ifdef _PRINT_QUALI_ARRAY
        OP << "Qualifier array at the final node:\n";
    for (unsigned i = 0; i < numNodes; i++)
    {
        OP << "index = " << i << ", qualifier = " << nQualiArray[endIns][i] << "\n";
    }
#endif
    OP << "begin to summarize funcs.\n";
    summarizeFuncs(RI);
//The list of the node
#ifdef ListsForNode
    OP << "Lists for each node:\n";
    for (unsigned i = 0; i < numNodes; i++)
    {
        if (!nodeFactory.getWL(i).empty() && !nodeFactory.getBL(i).empty())
        {
            OP << "BL for node " << i << "\n";
            for (auto item : nodeFactory.getBL(i))
            {
                OP << item << "/";
            }
            OP << "\n WL for node " << i << "\n";
            for (auto item : nodeFactory.getWL(i))
            {
                OP << item << "/";
            }
        }
    }
#endif
}

void FuncAnalysis::computeQualifier(llvm::Instruction *I, std::vector<int> &in, std::vector<int> &out)
{
    //OP<<"Compute qualifier for "<<*I<<"\n";
    unsigned numNodes = nodeFactory.getNumNodes();
    Instruction *entry = &(F->front().front());
    NodeIndex entryNode = nodeFactory.getValueNodeFor(entry);
    //for all instructions out = in
    out.assign(in.begin(), in.end());
    ReturnInst *RI = NULL;
#ifdef _PRINT_INST2
    OP << *I << "\n";
#endif
//if (nodeFactory.getNumNodes() > 839)
//OP<<"in[839] = "<<in[839]<<"\n";
#ifdef INOUT
    OP << "=============================in==========================\n";
    for (unsigned i = 0; i < numNodes; i++)
    {
        OP << "index = " << i << ": " << in[i] << "\t";
    }
#endif
    std::set<const llvm::Value *> reqVisit;
    std::string insStr;
    llvm::raw_string_ostream rso(insStr);
    I->print(rso);

    switch (I->getOpcode())
    {
        case Instruction::Alloca:
        {
            if (VisitIns.find(I) != VisitIns.end())
                break;
            NodeIndex valIndex = nodeFactory.getValueNodeFor(I);
            //set name for the valIndex
            size_t pos1 = insStr.find('%');
            size_t pos2 = insStr.find('=');
            //OP<<"pos1 = "<<pos1<<", pos2 = "<<pos2<<"\n";
            std::string ptrName = insStr.substr(pos1, pos2 - 3);
            NodeIndex objIndex = AndersNodeFactory::InvalidIndex;
            assert(valIndex != AndersNodeFactory::InvalidIndex && "Failed to find alloca value node");

            out.at(valIndex) = _ID;

            assert(I->getType()->isPointerTy());
            const Type *type = cast<PointerType>(I->getType())->getElementType();

            // An array is considered a single variable of its type.
            while (const ArrayType *arrayType = dyn_cast<ArrayType>(type))
                type = arrayType->getElementType();

            // Now construct the pointer and memory object variable
            // It depends on whether the type of this variable is a struct or not

            if (const StructType *stType = dyn_cast<StructType>(type))
            {
                //set each of the field to _UDs
                // Sanity check
                assert(stType != NULL && "structType is NULL");

                const StructInfo *stInfo = Ctx->structAnalyzer.getStructInfo(stType, M);
                assert(stInfo != NULL && "structInfoMap should have info for all structs!");
                if (stInfo->isEmpty())
                {
                    break;
                }
                objIndex = nodeFactory.getObjectNodeFor(I);
                assert(objIndex != AndersNodeFactory::InvalidIndex && "Failed to find alloca obj node");
                // Non-empty structs
                uint64_t stSize = stInfo->getExpandedSize();

                for (unsigned i = 1; i < stSize; ++i)
                {
                    //OP<<"struct process, i = "<<i<<"\n";
                    out.at(objIndex + i) = _UD;
                }
            }
            objIndex = nodeFactory.getObjectNodeFor(I);
            assert(objIndex != AndersNodeFactory::InvalidIndex && "Failed to find alloca obj node");
            out.at(objIndex) = _UD;
#ifdef OUTQ
            OP << "related qualifier out[" << valIndex << "] = " << out[valIndex] << "\n";
#endif
            break;
        }
        case Instruction::Load:
        {
            //val = load from op
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find load operand node");

            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find load value node");

            if (srcNode <= nodeFactory.getConstantIntNode())
            {
                out.at(dstNode) = _ID;
                break;
            }
            //OP<<"srcNode = "<<srcNode<<", in["<<srcNode<<"] = "<<in[srcNode]<<"\n";
            //if the pointer is unknown or uninitialized, then the qualifier of the data should be
            //the same as it
#ifdef load_check
            OP << "opIndex = " << opIndex << "\n";
        OP << "[" << opIndex << "]: point to: \n";
        for (auto item : nPtsGraph[I][opIndex])
            OP << item << ", ";
        OP << "\n";
        OP << "out[" << valIndex << "]:\n";
        for (auto item : nPtsGraph[I][valIndex])
            OP << item << ", ";
        OP << "\n";
#endif
            //OP<<"srcNode = "<<srcNode<<", qualifier = "<<in.at(srcNode)<<"\n";
            if (in[srcNode] == _UNKNOWN)
            {
                reqVisit.clear();
                setReqFor(I, I->getOperand(0), out, reqVisit);
                //out.at(srcNode) = _ID;
                //backPropagateReq(I, I->getOperand(0), out);
            }

            if (out.at(srcNode) == _UD)
            {
                out.at(dstNode) = out.at(srcNode);
            }
            else
            {
                bool init = false;
                for (auto i : nPtsGraph[I][srcNode])
                {
                    //OP<<"i = "<<i<<", out: "<<out.at(i)<<"\n";
                    if (out.at(i) == _UD)
                    {
                        out.at(dstNode) = _UD;
                        break;
                    }

                    if (out[i] == _UNKNOWN)
                    {
                        for (auto aa : nAAMap[I][i])
                        {
                            relatedNode[dstNode].insert(aa);
                            relatedNode[dstNode].insert(relatedNode[aa].begin(), relatedNode[aa].end());
#ifdef _RELATED
                            OP << "relatedNode[" << dstNode << "].insert(" << aa << ")\n";
                        OP << "dstNode = " << dstNode << "\n";
                        for (auto it : relatedNode[dstNode])
                        {
                            if (it > entryNode)
                                continue;
                            OP << it << "/";
                        }
                        OP << "\n";
#endif
                        }
                    }

                    if (!init)
                    {
                        out.at(dstNode) = out.at(i);
                        init = true;
                    }
                    else
                    {
                        out.at(dstNode) = std::min(out.at(dstNode), out.at(i));
                    }
                }
            }
#ifdef OUTQ
            OP << "related qualifier out[" << dstNode << "] = " << out[dstNode] << "\n";

#endif
            break;
        }
        case Instruction::Store:
        {
            //OP<<"numNodes = "<<nodeFactory.getNumNodes()<<"\n";
            NodeIndex srcNode = nodeFactory.getValueNodeFor(I->getOperand(0));

            if (srcNode == AndersNodeFactory::InvalidIndex)
            {
                // If we hit the store insturction like below, it is
                // possible that the global variable (init_user_ns) is
                // an extern variable. Hope this does not happen in kcfi,
                // otherwise we need to assume the worst case :-(

                // 1. store %struct.user_namespace* @init_user_ns,
                // %struct.user_namespace**  %from.addr.i, align 8
                // 2. @init_user_ns = external global %struct.user_namespace
                break;
            }
            //assert(srcIndex != AndersNodeFactory::InvalidIndex && "Failed to find store src node");
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I->getOperand(1));

            bool singleEle = false;
            //check if %dst is one element of the array
            if (GetElementPtrInst *GEPInst = dyn_cast<GetElementPtrInst>(I->getOperand(1)))
            {
                llvm::Type *T = GEPInst->getOperand(0)->getType();
                const Type *type = cast<PointerType>(T)->getElementType();
                if (const ArrayType *arrayType = dyn_cast<ArrayType>(type))
                {
                    singleEle = true;
                }
            }

            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find store dst node");
            //OP<<"srcIndex = "<<srcNode<<", dstIndex = "<<dstNode<<"\n";
            //OP<<"srcNode = "<<srcNode<<", quali = "<<in.at(srcNode)<<"\n";
            //1.%dst comes from arg
            int qualiSrc = out.at(srcNode);
            if (const ConstantExpr *cexpr = dyn_cast<ConstantExpr>(I->getOperand(0)))
            {
                qualiSrc = getQualiForConstant(cexpr, nodeFactory, in);
            }
            //OP<<"out.at("<<srcNode<<") = "<<out.at(srcNode)<<"\n";
            for (auto item : nPtsGraph[I][dstNode])
            {
                //OP<<"item = "<<item<<"\n";
                if (nodeFactory.isArgNode(item))
                {
                    relatedNode[item].insert(srcNode);
                    relatedNode[item].insert(relatedNode[srcNode].begin(), relatedNode[srcNode].end());
#ifdef _RELATED
                    OP << "item = " << item << "\n";
                for (auto it : relatedNode[item])
                    OP << it << "/";
                OP << "\n";
#endif
                }
            }
            //OP<<"1\n";
            if (out.at(dstNode) == _UNKNOWN || nodeFactory.isArgNode(dstNode))
            {
                //caae1: store %arg1, %arg2
                if (qualiSrc == _UNKNOWN || nodeFactory.isArgNode(srcNode))
                {
                    for (auto i : nPtsGraph[I][dstNode])
                    {
                        if (i <= nodeFactory.getConstantIntNode())
                            continue;
                        relatedNode[i].insert(srcNode);
                        relatedNode[i].insert(nAAMap[I][srcNode].begin(), nAAMap[I][srcNode].end());
#ifdef _RELATED
                        OP << "relatedNode[" << i << "].insert(" << srcNode << ")\n";
                    for (auto item : relatedNode[i])
                        OP << item << "/";
                    OP << "\n";
#endif
                    }
                }
#ifdef MV
                if (nodeFactory.isHeapNode(dstNode))
            {
                reqVisit.clear();
                setReqFor(I, I->getOperand(1), out, reqVisit);
                out.at(dstNode) = _ID;
            }
#endif
                reqVisit.clear();
                setReqFor(I, I->getOperand(1), out, reqVisit);
                out.at(dstNode) = _ID;
                //backPropagateReq(I, (I->getOperand(1)), out);
// %src-para && %dst-para
#ifdef INSENS
                if (in.at(srcNode) == _UNKNOWN)
            {
                if (srcNode > nodeFactory.getConstantIntNode())
                {
                    reqVisit.clear();
                    setReqFor(I, I->getOperand(0), out, reqVisit);
                }
                //backPropagateReq(I, (I->getOperand(0)), out);
                for (auto obj : nPtsGraph[I][dstNode])
                {
                    out.at(obj) = _ID;
                }
                break;
            }
#endif
                //%src-global/stack &&dst-para
                for (auto i : nPtsGraph[I][dstNode])
                {
                    if (i <= nodeFactory.getConstantIntNode() || singleEle)
                        continue;
                    out.at(i) = qualiSrc;
                }
                break;
            }

            //2. %dst comes from global or heap:
            if (dstNode <= nodeFactory.getUniversalObjNode() || nodeFactory.isHeapNode(dstNode))
            {
                if (in.at(srcNode) == _UNKNOWN)
                {
                    reqVisit.clear();
                    setReqFor(I, I->getOperand(0), out, reqVisit);
                    //backPropagateReq(I, (I->getOperand(0)), out);
                }
                break;
            }
            //3. other cases:
            for (auto i : nPtsGraph[I][dstNode])
            {
                //OP<<"numNodes = "<<nodeFactory.getNumNodes()<<"\n";
                if (i <= nodeFactory.getConstantIntNode() || singleEle)
                    continue;
                out.at(i) = qualiSrc;
#ifdef OUTQ
                OP << "related qualifier out[" << i << "] = " << out[i] << "\n";
#endif
            }
            //Check if sth is stored to the arg, then set the changeVec to _CH
            for (auto obj : nPtsGraph[I][dstNode])
            {
                if (nodeFactory.isArgNode(obj))
                {
                    nodeFactory.setStored(obj, _CH);
                }
            }
            break;
        }
        case Instruction::GetElementPtr:
        {
            assert(I->getType()->isPointerTy());

            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(srcIndex != AndersNodeFactory::InvalidIndex && "Failed to find gep src node");
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find gep dst node");

            int64_t offset = getGEPOffset(I, DL);
            int64_t fieldNum = 0;
            bool onlyUnion = true;
            for (auto obj : nPtsGraph[I][dstIndex])
            {
                if (obj <= nodeFactory.getConstantIntNode())
                    continue;
                if (!nodeFactory.isUnOrArrObjNode(obj))
                {
                    onlyUnion = false;
                }
            }
            if (!onlyUnion)
                fieldNum = offsetToFieldNum(I->getOperand(0)->stripPointerCasts(), offset, DL,
                                            &Ctx->structAnalyzer, M);

            int qualiSrc = in.at(srcIndex);
            if (const ConstantExpr *cexpr = dyn_cast<ConstantExpr>(I->getOperand(0)))
                qualiSrc = getQualiForConstant(cexpr, nodeFactory, in);

            out.at(dstIndex) = qualiSrc;
            for (int i = 0; i < I->getNumOperands(); i++)
            {
                NodeIndex opIndex = nodeFactory.getValueNodeFor(I->getOperand(i));
                if (out.at(opIndex) == _UNKNOWN)
                    relatedNode[dstIndex].insert(opIndex);
            }

            //If the offset < 0, we need to copy the origin qualifer to the new node.
            if (offset < 0)
            {
                for (auto item : inPtsGraph[I][srcIndex])
                {
                    unsigned itemSize = nodeFactory.getObjectSize(item);
                    for (auto obj : nPtsGraph[I][srcIndex])
                    {
                        if (item <= nodeFactory.getConstantIntNode() || obj <= nodeFactory.getConstantIntNode())
                            continue;
                        unsigned objSize = nodeFactory.getObjectSize(obj);
                        if (itemSize < objSize)
                        {
                            for (unsigned i = 0; i < itemSize; i++)
                            {
                                out.at(obj + i) = in.at(item + i);
                            }
                        }
                    }
                }
            }
#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::Add:
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
        {
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            NodeIndex op0Index = nodeFactory.getValueNodeFor(I->getOperand(0));
            NodeIndex op1Index = nodeFactory.getValueNodeFor(I->getOperand(1));
            if (isa<ConstantInt>(I->getOperand(0)))
            {
                ConstantInt *ci = dyn_cast<ConstantInt>(I->getOperand(0));
            }
            if (isa<ConstantInt>(I->getOperand(1)))
            {
                ConstantInt *ci = dyn_cast<ConstantInt>(I->getOperand(1));
            }

            out.at(dstIndex) = std::min(in.at(op0Index), in.at(op1Index));
            if (in.at(op0Index) == _UNKNOWN)
            {
                relatedNode[dstIndex].insert(op0Index);
                relatedNode[dstIndex].insert(relatedNode[op0Index].begin(), relatedNode[op0Index].end());
            }
            if (in.at(op1Index) == _UNKNOWN)
            {
                relatedNode[dstIndex].insert(op1Index);
                relatedNode[dstIndex].insert(relatedNode[op1Index].begin(), relatedNode[op1Index].end());
            }

#ifdef _RELATED
            OP << "Related nodes:\n";
        for (auto item : relatedNode[dstIndex])
            OP << item << ", ";
        OP << "\n";
#endif

//out[dstIndex] = max(out[dstIndex], _UD);
#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::ICmp:
        {
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            NodeIndex op0Index = nodeFactory.getValueNodeFor(I->getOperand(0));
            NodeIndex op1Index = nodeFactory.getValueNodeFor(I->getOperand(1));

            if (out.at(op0Index) == _UNKNOWN)
            {
                reqVisit.clear();
                setReqFor(I, I->getOperand(0), out, reqVisit);
                //out.at(op0Index) = _ID;
                //backPropagateReq(I, I->getOperand(0), out);
            }
            if (out.at(op1Index) == _UNKNOWN)
            {
                reqVisit.clear();
                setReqFor(I, I->getOperand(1), out, reqVisit);
                //out.at(op1Index) = _ID;
                //backPropagateReq(I, I->getOperand(1), out);
            }
            out.at(dstIndex) = std::min(in.at(op0Index), in.at(op1Index));

            if (isa<ConstantInt>(I->getOperand(0)))
            {
                ConstantInt *ci = dyn_cast<ConstantInt>(I->getOperand(0));
                int val = ci->getSExtValue();
            }
            if (isa<ConstantInt>(I->getOperand(1)))
            {
                ConstantInt *ci = dyn_cast<ConstantInt>(I->getOperand(1));
                int val = ci->getSExtValue();
            }

#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::Br:
        {
            const BranchInst *brInst = cast<BranchInst>(I);
            if (I->getNumOperands() == 3)
            {
                NodeIndex condIndex = nodeFactory.getValueNodeFor(brInst->getCondition());
                if (out.at(condIndex) == _UNKNOWN)
                {
                    reqVisit.clear();
                    setReqFor(I, brInst->getCondition(), out, reqVisit);
                    out.at(condIndex) = _ID;
                    //backPropagateReq(I, brInst->getCondition(), out);
                }
            }
            break;
        }
        case Instruction::SExt:
        case Instruction::ZExt:
        {
            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            out.at(dstIndex) = in.at(srcIndex);
            relatedNode[dstIndex].insert(relatedNode[srcIndex].begin(), relatedNode[srcIndex].end());

#ifdef _RELATED
            OP << "Related nodes:\n";
        for (auto item : relatedNode[dstIndex])
            OP << item << ", ";
        OP << "\n";
#endif

#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::PHI:
        {
            const PHINode *phiInst = cast<PHINode>(I);
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(phiInst);
            assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find phi dst node");
            NodeIndex initIndex = nodeFactory.getValueNodeFor(phiInst->getIncomingValue(0));
            assert(initIndex != AndersNodeFactory::InvalidIndex && "Failed to find phi init node");
            //OP<<"initIndex in["<<initIndex<<"]: "<<in[initIndex]<<"\n";
            std::string nameStr = "phi";

            bool init = false;
            for (unsigned i = 0, e = phiInst->getNumIncomingValues(); i != e; ++i)
            {
                Value *value = phiInst->getIncomingValue(i);

                if (Instruction *ins = dyn_cast<Instruction>(value))
                {
                    if (nQualiArray.find(ins) == nQualiArray.end())
                        continue;
                }
                NodeIndex srcIndex = nodeFactory.getValueNodeFor(phiInst->getIncomingValue(i));

                //OP<<"incomming edge "<<i<<", initIndex in["<<srcIndex<<"]: "<<in[srcIndex]<<"\n";
                assert(srcIndex != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
                if (isa<ConstantInt>(value))
                {
                    ConstantInt *ci = dyn_cast<ConstantInt>(value);
                    int val = ci->getSExtValue();
                }

                if (!init)
                {
                    init = true;
                    out.at(dstIndex) = in.at(srcIndex);
                }
                else
                {
                    out.at(dstIndex) = std::min(out.at(dstIndex), in.at(srcIndex));
                }
            }
#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::BitCast:
        case Instruction::Trunc:
        {
            //OP<<"numnodes = "<<nodeFactory.getNumNodes()<<"\n";
            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(srcIndex != AndersNodeFactory::InvalidIndex && "Failed to find bitcast src node");
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find bitcast dst node");

            //cp the qualifier from before to after, assume there's one obj
            relatedNode[dstIndex].insert(relatedNode[srcIndex].begin(), relatedNode[srcIndex].end());
#ifdef _RELATED
            OP << "Related nodes:\n";
        for (auto item : relatedNode[dstIndex])
            OP << item << ", ";
        OP << "\n";
#endif
            for (auto srcObj : inPtsGraph[I][srcIndex])
            {
                if (srcObj <= nodeFactory.getConstantIntNode())
                    continue;
                unsigned objSize = nodeFactory.getObjectSize(srcObj);
                for (auto dstObj : nPtsGraph[I][srcIndex])
                {
                    if (srcObj <= nodeFactory.getConstantIntNode() || dstObj <= nodeFactory.getConstantIntNode())
                        continue;
                    unsigned dstObjSize = nodeFactory.getObjectSize(dstObj);
                    if (dstObjSize > objSize)
                    {
                        for (unsigned i = 0; i < objSize; i++)
                        {
                            out.at(dstObj + i) = in.at(srcObj + i);
                        }
                    }
                }
            }

            out.at(dstIndex) = in.at(srcIndex);
            if (VisitIns.find(I) != VisitIns.end())
                break;
            if (Instruction *Ins = dyn_cast<Instruction>(I->getOperand(0)))
            {
                if (CallInst *CI = dyn_cast<CallInst>(Ins))
                {
                    if (CI->getCalledFunction())
                    {
                        StringRef fName = CI->getCalledFunction()->getName();
                        if (Ctx->HeapAllocFuncs.count(fName.str()))
                        {
                            for (auto dstObj : nPtsGraph[I][srcIndex])
                            {
                                if (dstObj <= nodeFactory.getConstantIntNode())
                                    continue;
                                unsigned objSize = nodeFactory.getObjectSize(dstObj);
                                for (unsigned i = 0; i < objSize; i++)
                                {
                                    nodeFactory.setHeapNode(dstObj + i);
                                    if (Ctx->ZeroMallocFuncs.count(fName.str())) {
                                        out.at(dstObj + i) = _ID;
                                    }
                                    else {
                                        out.at(dstObj + i) = _UD;
                                    }
                                }
                            }
                        }
                    }
                }
            }
#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::IntToPtr:
        {
            assert(I->getType()->isPointerTy());
            // Get the node index for dst
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find inttoptr dst node");

            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(srcIndex != AndersNodeFactory::InvalidIndex && "Failed to find inttoptr src node");
            out.at(dstIndex) = in.at(srcIndex);
#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::PtrToInt:
        {
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find ptrtoint dst node");
            if (srcIndex != AndersNodeFactory::InvalidIndex)
            {
                out.at(dstIndex) = in.at(srcIndex);
            }

#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::Select:
        {
            const SelectInst *selectInst = cast<SelectInst>(I);

            NodeIndex srcIndex1 = nodeFactory.getValueNodeFor(I->getOperand(1));
            assert(srcIndex1 != AndersNodeFactory::InvalidIndex && "Failed to find select src node 1");
            NodeIndex srcIndex2 = nodeFactory.getValueNodeFor(I->getOperand(2));
            assert(srcIndex2 != AndersNodeFactory::InvalidIndex && "Failed to find select src node 2");
            NodeIndex conditionIndex = nodeFactory.getValueNodeFor(selectInst->getCondition());
            assert(conditionIndex != AndersNodeFactory::InvalidIndex && "Failed to find select condition node");
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find select dst node");
            out.at(dstIndex) = std::min(in.at(srcIndex1), in.at(srcIndex2));
            out.at(dstIndex) = std::min(in.at(conditionIndex), out.at(dstIndex));


            if (isa<ConstantInt>(I->getOperand(1)))
            {
                ConstantInt *ci = dyn_cast<ConstantInt>(I->getOperand(1));
                int val = ci->getSExtValue();
            }
            if (isa<ConstantInt>(I->getOperand(2)))
            {
                ConstantInt *ci = dyn_cast<ConstantInt>(I->getOperand(2));
                int val = ci->getSExtValue();
            }
#ifdef OUTQ
            OP << "related qualifier out[" << dstIndex << "] = " << out[dstIndex] << "\n";
#endif
            break;
        }
        case Instruction::ExtractValue:
        {
            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
            if (CallInst *CI = dyn_cast<CallInst>(I->getOperand(0)))
            {
                if (CI->isInlineAsm())
                {
                    out.at(dstIndex) = in.at(srcIndex);
                }
            }
            if (out.at(dstIndex) == _UNKNOWN)
                relatedNode[dstIndex].insert(srcIndex);
            break;
        }
        case Instruction::VAArg:
        {
            if (I->getType()->isPointerTy())
            {
                NodeIndex dstIndex = nodeFactory.getValueNodeFor(I);
                assert(dstIndex != AndersNodeFactory::InvalidIndex && "Failed to find va_arg dst node");
                NodeIndex vaIndex = nodeFactory.getVarargNodeFor(I->getParent()->getParent());
                assert(vaIndex != AndersNodeFactory::InvalidIndex && "Failed to find vararg node");
                out.at(dstIndex) = in.at(vaIndex);
            }
            break;
        }
        case Instruction::Call:
        {
            if (isa<DbgInfoIntrinsic>(I))
            {
                //OP<<"do nothing about dbgInfoIntrinsic: "<<*I<<"\n";
                break;
            }
            CallInst *CI = dyn_cast<CallInst>(I);
            OP << *CI << "\n";
            NodeIndex dstNode = nodeFactory.getValueNodeFor(I);
            assert(dstNode != AndersNodeFactory::InvalidIndex && "Failed to find call dst node");
#ifdef CALL_DBG
            for (int argNo = 0; argNo < CI->getNumArgOperands(); argNo++)
        {
            NodeIndex argIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
            if (!(CI->getArgOperand(argNo)->getType())->isPointerTy())
                continue;
            //OP<<"argIndex = "<<argIndex<<"\n";
            const Type *type = cast<PointerType>(CI->getArgOperand(argNo)->getType())->getElementType();

            // An array is considered a single variable of its type.
            while (const ArrayType *arrayType = dyn_cast<ArrayType>(type))
                type = arrayType->getElementType();

            if (const StructType *structType = dyn_cast<StructType>(type))
            {
                if (structType->isOpaque())
                {
                    continue;
                }

                const StructInfo *stInfo = Ctx->structAnalyzer.getStructInfo(structType, M);
                uint64_t stSize = stInfo->getExpandedSize();
                //OP<<"qualifier of argIndex: "<<in[argIndex]<<"\n";
                for (auto obj : nPtsGraph[I][argIndex])
                {
                    for (uint64_t i = 0; i < stSize; i++)
                    //OP<<"qualifier of node in["<<obj + i<<"] = "<<in[obj+i]<<"\n";
                }
            }
        }
#endif
            //1. process the assembly
            if (CI->isInlineAsm())
            {
                //OP<<"asm\n";
                //OP<<"getNumArgOperands() = "<<CI->getNumArgOperands()<<"\n";
                InlineAsm *ASM = dyn_cast<InlineAsm>(CI->getCalledValue());
                InlineAsm::ConstraintInfoVector CIV = ASM->ParseConstraints();
                //check if all the input are init
                bool init = true;
                for (int argNo = 0; argNo < CI->getNumArgOperands(); argNo++)
                {
                    NodeIndex argNode = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
                    Value *argValue = CI->getArgOperand(argNo);
                    InlineAsm::ConstraintInfo consInfo = CIV.at(argNo);
                    if (consInfo.Type == InlineAsm::isInput)
                    {
                        //OP<<"in["<<argNode<<"] = "<<in[argNode]<<"\n";
                        //OP << *argValue << "\n";
                        if (out.at(argNode) == _UNKNOWN)
                        {
                            reqVisit.clear();
                            setReqFor(I, argValue, out, reqVisit);
                            out.at(argNode) = _ID;
                            //backPropagateReq(I, argValue, out);
                        }

                        if (out.at(argNode) != _ID)
                        {
                            init = false;
                            break;
                        }
                    }
                    //const std::string str = ASM->getConstraintString();
                }
                std::string insStr;
                llvm::raw_string_ostream rso(insStr);
                I->print(rso);
                if (insStr.find("pushsection .discard.reachable") != std::string::npos) addTerminationBB(I->getParent());

                //if some of the ndoes are uninit, then the output should be uninit
                int srcQuali = _ID;
                if (!init)
                {
                    srcQuali = _UD;
                }
                for (int argNo = 0; argNo < CI->getNumArgOperands(); argNo++)
                {
                    //set the qualifier of the output value.
                    NodeIndex argNode = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
                    Value *argValue = CI->getArgOperand(argNo);
                    if (argNode > nodeFactory.getConstantIntNode())
                        out[argNode] = srcQuali;
                    InlineAsm::ConstraintInfo consInfo = CIV.at(argNo);
                    if (consInfo.Type == InlineAsm::isOutput)
                    {
                        //OP<<"argNode = "<<argNode<<"\n";
                        for (auto obj : nPtsGraph[I][argNode])
                        {
                            //OP<<"obj = "<<obj<<"\n";
                            if (obj <= nodeFactory.getConstantIntNode())
                                continue;
                            out.at(obj) = srcQuali;
                        }
                    }
                    //const std::string str = ASM->getConstraintString();
                }
                out.at(dstNode) = srcQuali;
                //OP<<"dstNode = "<<dstNode<<"\n";;
                for (auto obj : nPtsGraph[I][dstNode])
                {
                    if (obj <= nodeFactory.getConstantIntNode())
                        break;
                    int objSize = nodeFactory.getObjectSize(obj);
                    //OP<<"obj = "<<obj<<", objSize = "<<objSize<<"\n";
                    for (int i = 0; i < objSize; i++)
                    {
                        //OP<<"i = "<<i<<", obj+i = "<<obj+i<<"\n";
                        out.at(obj + i) = srcQuali;
                    }
                }
                //OP<<"end of asm.\n";
                break;
            }
            //2. Objsize Function, update the pointer qualifier to be initialized
            if (CI->getCalledFunction())
            {
                StringRef fName = CI->getCalledFunction()->getName();
                //OP<<"fName:"<<fName.str()<<"\n";
                if (Ctx->ObjSizeFuncs.count(fName.str()))
                {
                    out.at(dstNode) = _ID;
                    break;
                }
            }
            bool memsetUse = false, retCheck = false;

            for (Use &U : I->uses())
            {
                Instruction *Ins = dyn_cast<Instruction>(U.getUser());
                if (CallInst *CI = dyn_cast<CallInst>(Ins))
                {
                    if (CI->getCalledFunction() && Ctx->InitFuncs.count(CI->getCalledFunction()->getName().str()))
                        memsetUse = true;
                }
            }
            llvm::Function *Func = NULL;
            if (CI->getCalledFunction())
                Func = CI->getCalledFunction();
            else
            {
                if (Ctx->Callees.find(CI) != Ctx->Callees.end() && (!Ctx->Callees[CI].empty()))
                {
                    FuncSet::iterator iter = Ctx->Callees[CI].begin();
                    Func = *iter;
                }
            }
            if (Func)
            {
                //OP<<*I<<"\n";
                StringRef fName = Func->getName();
                //OP << "possible function:" <<Func<<": "<<fName.str() << ", scopeName: " << getScopeName(Func, Ctx->funcToMd, Ctx->Funcs) << "\n";
                if (Ctx->HeapAllocFuncs.count(fName.str()))
                {
                    out.at(dstNode) = _ID;
                    int quali = _UD;
                    //If the return is checked, we set the quali to _ID
                    for (User *U : I->users())
                    {
                        Instruction *Ins = dyn_cast<Instruction>(U);
                        //OP<<"Ins = "<<*Ins<<"\n";
                        if (ICmpInst *ICI = dyn_cast<ICmpInst>(Ins)) {
                            Value *cmp = ICI->getOperand(1);
                            if (ConstantPointerNull *cpn = dyn_cast<ConstantPointerNull>(cmp)) {
                                retCheck = true;
                            }
                            else if (ConstantInt *cmp = dyn_cast<ConstantInt>(cmp)) {
                                retCheck = true;
                            }
                        }
                        if (StoreInst *SI = dyn_cast<StoreInst>(Ins)) {
                            for (User *UU : SI->getPointerOperand()->users()) {
                                //OP<<"UU :"<<*UU<<"\n";
                                if (ConstantExpr *CE = dyn_cast<ConstantExpr>(UU))
                                    continue;
                                Instruction *UseIns = dyn_cast<Instruction>(UU);
                                if (LoadInst *LI = dyn_cast<LoadInst>(UseIns))
                                {
                                    for (User *LIU : LI->users()) {
                                        //OP<<"LIU = "<<*LIU<<"\n";
                                        Instruction *LUseIns = dyn_cast<Instruction>(LIU);
                                        //OP<<"LUseIns = "<<*LUseIns<<"\n";
                                        if (ICmpInst *ICI = dyn_cast<ICmpInst>(LUseIns)) {
                                            Value *cmp = ICI->getOperand(1);
                                            NodeIndex cmpIndex = nodeFactory.getValueNodeFor(cmp);
                                            //OP<<"cmp: "<<*cmp<<", cmpIndex = "<<cmpIndex<<"\n";
                                            if (cmpIndex > nodeFactory.getConstantIntNode()) continue;
                                            if (cmpIndex == nodeFactory.getConstantIntNode()){
                                                retCheck = true;
                                            }
                                            else if (ConstantPointerNull *cpn = dyn_cast<ConstantPointerNull>(cmp)) {
                                                retCheck = true;
                                            }
                                            else if (ConstantInt *cmp = dyn_cast<ConstantInt>(cmp)) {
                                                retCheck = true;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Value *FlagArg = NULL;
                    if (fName.str() == "vzalloc"||fName.str() == "vmalloc") {
                        //do nothing
                    }
                    else if (fName.str() == "krealloc")
                        FlagArg = CI->getArgOperand(2);
                    else if (CI->getNumArgOperands() > 1){
                        FlagArg = CI->getArgOperand(1);
                    }
                    std::string str = "zalloc";
                    if (fName.str().find(str) != std::string::npos || memsetUse || retCheck)
                    {
                        quali = _ID;
                    }
                    else if (FlagArg) {
                        if (ConstantInt *CFlagArg =
                                    dyn_cast<ConstantInt>(FlagArg)) {
                            // If ___GFP_ZERO is used, the heap allocation is already
                            // initialized. In this case, it is safe, so we skip it.
                            //  #define ___GFP_ZERO   0x8000u
                            if (CFlagArg->getZExtValue() & 0x8000u)
                                quali = _ID;
                        }
                    }
                    for (auto obj : nPtsGraph[I][dstNode])
                    {
                        if (obj <= nodeFactory.getConstantIntNode())
                            continue;
                        unsigned objSize = nodeFactory.getObjectSize(obj);
                        for (unsigned i = 0; i < objSize; i++)
                        {
                            nodeFactory.setHeapNode(obj + i);
                            out.at(obj + i) = quali;
                        }
                    }
                }
                else if (Ctx->InitFuncs.count(fName.str()))
                {
                    OP << "process init funcs\n";
                    processInitFuncs(I, Func, false, in, out);
                }
                else if (Ctx->CopyFuncs.count(fName.str()))
                {
                    OP << "process memcpy funcs\n";
                    processCopyFuncs(I, Func, false, in, out);
                }
                else if (Ctx->TransferFuncs.count(fName.str()))
                {
                    OP << "process transfer funcs\n";
                    processTransferFuncs(I, Func, false, in, out);
                }
                else if (Ctx->OtherFuncs.count(fName.str()))
                {
                    //do nothing
                }
                else
                {
                    OP << "process  funcs\n";

                    processFuncs(I, Func, false, in, out);
                    OP << "end of process funcs.\n";
                }
            }
            if (!CI->getCalledFunction() && (Ctx->Callees.find(CI) != Ctx->Callees.end()))
            {
                bool init = false;
                OP << *I << ", possible # of targets: "<<Ctx->Callees[CI].size()<<"\n";
                for (auto func : Ctx->Callees[CI])
                {
                    if (!init)
                    {
                        init = true;
                        continue;
                    }
                    StringRef fName = func->getName();

                    if (Ctx->HeapAllocFuncs.count(fName.str()))
                    {
                        for (auto obj : nPtsGraph[I][dstNode])
                        {
                            if (obj <= nodeFactory.getConstantIntNode())
                                continue;
                            unsigned objSize = nodeFactory.getObjectSize(obj);
                            for (unsigned i = 0; i < objSize; i++)
                            {
                                nodeFactory.setHeapNode(obj + i);
                                out.at(obj + i) = _UD;
                            }
                        }
                    }
                    else if (Ctx->InitFuncs.count(fName.str()))
                    {
                        processInitFuncs(I, func, true, in, out);
                    }
                    else if (Ctx->CopyFuncs.count(fName.str()))
                        processCopyFuncs(I, func, true, in, out);
                    else if (Ctx->TransferFuncs.count(fName.str()))
                        processTransferFuncs(I, func, true, in, out);
                    else
                    {
                        OP << "processFuncs : " << func->getName().str() << "\n";
                        processFuncs(I, func, true, in, out);
                    }
                }
            }
#ifdef OUTQ
            OP << "related qualifier out[" << dstNode << "] = " << out[dstNode] << "\n";
    for (auto obj : nPtsGraph[I][dstNode])
    {
               if (obj <= nodeFactory.getConstantIntNode())
                    break;
                int objSize = nodeFactory.getObjectSize(obj);
                OP<<"obj = "<<obj<<", objSize = "<<objSize<<"\n";
                for (int i = 0; i < objSize; i++)
                {
                    OP<<"i = "<<i<<", obj+i = "<<obj+i<<": qualifier: "<<out.at(obj + i)<<"\n";
                }
            }
#endif
            break;
        }
        case Instruction::Ret:
        {
            RI = dyn_cast<ReturnInst>(I);
            if (!F->getReturnType()->isVoidTy())
            {
                NodeIndex fRetNode = nodeFactory.getReturnNodeFor(F);
                NodeIndex retNode = nodeFactory.getValueNodeFor(I->getOperand(0));
                //	OP<<"fRetNode = "<<fRetNode<<"\n";
                //	OP<<"retNode = "<<retNode<<"\n";
                if (retNode <= nodeFactory.getConstantIntNode())
                    out.at(fRetNode) = _ID;
                else
                {
#ifdef _INSENS
                    if (out.at(retNode) == _UNKNOWN)
                {
                    reqVisit.clear();
                    setReqFor(I, I->getOperand(0), out, reqVisit);
                    out.at(retNode) = _ID;
                    //backPropagateReq(I, I->getOperand(0), out);
                }
                for (auto obj : nPtsGraph[I][retNode])
                {
                    //		OP<<"obj = "<<obj<<"\n";
                    if (obj <= nodeFactory.getConstantIntNode())
                        continue;
                    unsigned objSize = nodeFactory.getObjectSize(obj);
                    unsigned objOffset = nodeFactory.getObjectOffset(obj);
                    //		OP<<"objSize = "<<objSize<<"\n";
                    for (unsigned i = 0; i < objSize - objOffset; i++)
                    {
                        if (out.at(obj + i) == _UNKNOWN)
                        {
                            out.at(obj + i) = _ID;
                            //DFS(I, obj + i);
                        }
                    }
                    for (unsigned i = 0; i < objOffset; i--)
                    {
                        if (out.at(obj - i) == _UNKNOWN)
                        {
                            out.at(obj - i) = _ID;
                            //DFS(I, obj - i);
                        }
                    }
                }
#endif
                    out.at(fRetNode) = out.at(retNode);
                    relatedNode[fRetNode] = relatedNode[retNode];
                }
            }

            break;
        }
        default:
        {
            if (I->getType()->isPointerTy())
                OP << "pointer-related inst not handled!" << *I << "\n";
            //WARNING("pointer-related inst not handled!" << *I << "\n");
            //assert(!inst->getType()->isPointerTy() && "pointer-related inst not handled!");
            break;
        }
    } //I -> getOpcode()
    //OP<<"4.5\n";
}
void FuncAnalysis::backPropagateReq(llvm::Instruction *currentIns, llvm::Value *Val, std::vector<int> &out)
{
    NodeIndex valNode = nodeFactory.getValueNodeFor(Val);
    //DFS(currentIns, valNode);
    for (auto aa : nAAMap[currentIns][valNode])
    {
        if (out.at(aa) == _UNKNOWN)
        {
            //DFS(currentIns, aa);
        }
    }
    //OP<<"back propagate : for "<<*Val<<" : "<<valNode<<"\n";

    if (Instruction *I = dyn_cast<Instruction>(Val))
    {
        if (isa<LoadInst>(I))
        {
            NodeIndex srcIndex = nodeFactory.getValueNodeFor(I->getOperand(0));
            for (auto obj : nPtsGraph[I][srcIndex])
            {
                if (nQualiArray[I].at(obj) == _UNKNOWN)
                {
                    nQualiArray[I].at(obj) = _ID;
                    //DFS(I, obj);
                }
            }
        }
        for (Use &U : I->operands())
        {
            if (Instruction *Ins = dyn_cast<Instruction>(U))
            {
                //OP<<"Def: "<<*Ins<<"\n";
                switch (Ins->getOpcode())
                {
                    case Instruction::Alloca:
                    {
                        NodeIndex node = nodeFactory.getObjectNodeFor(Ins);
                        break;
                    }
                    case Instruction::GetElementPtr:
                    {
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        //OP<<"inside gep, srcIndex =  "<<srcIndex<<" : "<<out[srcIndex]<<"\n";

                        if (out.at(srcIndex) == _UNKNOWN)
                        {
                            out.at(srcIndex) = _ID;
                            nQualiArray[Ins].at(srcIndex) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(0), out);
                        }
                        break;
                    }
                    case Instruction::Add:
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
                    case Instruction::ICmp:
                    {
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        NodeIndex op0Index = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        NodeIndex op1Index = nodeFactory.getValueNodeFor(Ins->getOperand(1));
                        if (out.at(op0Index) == _UNKNOWN)
                        {
                            out.at(op0Index) = _ID;
                            nQualiArray[Ins].at(op0Index) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(0), out);
                        }
                        if (out.at(op1Index) == _UNKNOWN)
                        {
                            out.at(op1Index) = _ID;
                            nQualiArray[Ins].at(op1Index) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(1), out);
                        }
                        break;
                    }
                    case Instruction::SExt:
                    case Instruction::ZExt:
                    case Instruction::BitCast:
                    case Instruction::Trunc:
                    case Instruction::IntToPtr:
                    case Instruction::PtrToInt:
                    {
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        if (out.at(srcIndex) == _UNKNOWN)
                        {
                            out.at(srcIndex) = _ID;
                            nQualiArray[Ins].at(srcIndex) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(0), out);
                        }
                        break;
                    }
                    case Instruction::Load:
                    {
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        //OP<<"Def :"<<*Ins<<" , load from "<<srcIndex<<"\n";
                        for (auto obj : nPtsGraph[Ins][srcIndex])
                        {
                            //OP<<"obj = "<<obj<<"\n";
                            for (auto aa : nAAMap[Ins][obj])
                            {
                                //OP<<"aa = "<<aa<<": "<<nQualiArray[Ins][aa]<<"\n";
                                if (nQualiArray[Ins].at(aa) == _UNKNOWN)
                                {
                                    nQualiArray[Ins].at(aa) = _ID;
                                    //DFS(Ins, aa);
                                    backPropagateReq(Ins, Ins->getOperand(0), out);
                                }
                            }
                        }
                        break;
                    }
                    case Instruction::PHI:
                    {
                        const PHINode *phiInst = cast<PHINode>(Ins);
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(phiInst);
                        for (unsigned i = 0; i < phiInst->getNumIncomingValues(); i++)
                        {
                            NodeIndex srcIndex = nodeFactory.getValueNodeFor(phiInst->getIncomingValue(i));
                            if (out.at(srcIndex) == _UNKNOWN)
                            {
                                out.at(srcIndex) = _ID;
                                nQualiArray[Ins].at(srcIndex) = _ID;
                                backPropagateReq(Ins, phiInst->getIncomingValue(i), out);
                            }
                        }
                        break;
                    }
                    case Instruction::Select:
                    {
                        NodeIndex conditionIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        NodeIndex srcIndex1 = nodeFactory.getValueNodeFor(Ins->getOperand(1));
                        NodeIndex srcIndex2 = nodeFactory.getValueNodeFor(Ins->getOperand(2));
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        if (out.at(conditionIndex) == _UNKNOWN)
                        {
                            out.at(conditionIndex) = _ID;
                            nQualiArray[Ins].at(conditionIndex) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(0), out);
                        }
                        if (out.at(srcIndex1) == _UNKNOWN)
                        {
                            out.at(srcIndex1) = _ID;
                            nQualiArray[Ins].at(srcIndex1) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(1), out);
                        }
                        if (out.at(srcIndex2) == _UNKNOWN)
                        {
                            out.at(srcIndex2) = _ID;
                            nQualiArray[Ins].at(srcIndex2) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(2), out);
                        }
                        break;
                    }
                    case Instruction::ExtractValue:
                    {
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        if (out[srcIndex] == _UNKNOWN)
                        {
                            out.at(srcIndex) = _ID;
                            nQualiArray[Ins].at(srcIndex) = _ID;
                            backPropagateReq(Ins, Ins->getOperand(0), out);
                        }
                        break;
                    }
                    case Instruction::Br:
                    {
                        const BranchInst *brInst = cast<BranchInst>(Ins);
                        if (I->getNumOperands() == 3)
                        {
                            NodeIndex condIndex = nodeFactory.getValueNodeFor(brInst->getCondition());
                            if (out.at(condIndex) == _UNKNOWN)
                            {
                                out.at(condIndex) = _ID;
                                nQualiArray[Ins].at(condIndex) = _ID;
                                backPropagateReq(Ins, brInst->getCondition(), out);
                            }
                        }
                        break;
                    }
                    default:
                    {
                        return;
                    }
                } //switch Opcode
            }
        }
    }
    else
    {
        out.at(valNode) = _ID;
    }
    return;
}
void FuncAnalysis::summarizeFuncs(llvm::ReturnInst *RI)
{
    OP << "inside summarize Funcs:\n";
    //1.set the eequirement argument
    Instruction *entry = &(F->front().front());
    Instruction *end = &(F->back().back());
    unsigned numNodes = nodeFactory.getNumNodes();
    //OP<<"1\n";

    //copy the requirement of arg to the function summary
    for (auto &a : F->args())
    {
        Argument *arg = &a;
        NodeIndex argIndex = nodeFactory.getValueNodeFor(arg);
        NodeIndex sumArgIndex = fSummary.sumNodeFactory.getValueNodeFor(arg);
        //OP<<"argIndex = "<<argIndex<<", sumArgIndex = "<<sumArgIndex<<"\n";
        if (qualiReq.at(argIndex) == _ID)
        {
            fSummary.reqVec.at(sumArgIndex) = _ID;
        }
        NodeIndex sumArgObjIndex = fSummary.sumNodeFactory.getObjectNodeFor(arg);
        if (sumArgObjIndex == AndersNodeFactory::InvalidIndex)
            continue;
        unsigned sumObjSize = fSummary.sumNodeFactory.getObjectSize(sumArgObjIndex);
        unsigned sumObjOffset = fSummary.sumNodeFactory.getObjectOffset(sumArgObjIndex);
        for (auto obj : nPtsGraph[entry][argIndex])
        {
            if (obj <= nodeFactory.getConstantIntNode())
                continue;
            for (unsigned i = 0; i < sumObjSize; i++)
            {
                //OP<<"i = "<<i<<", obj - sumObjOffset + i ="<<obj - sumObjOffset +i<<"\n";
                //copy the requirement
                if (qualiReq.at(obj - sumObjOffset + i) == _ID)
                {
                    //OP<<"sumArgObjIndex - sumObjOffset + i = "<<sumArgObjIndex - sumObjOffset + i<<"\n";
                    fSummary.reqVec.at(sumArgObjIndex - sumObjOffset + i) = _ID;
                }
            }
        }
    } //F->args()
    NodeIndex entryNode = nodeFactory.getValueNodeFor(entry);
#ifdef dbg
    for (int i = 0; i < entryNode; i++)
    {
        nodeFactory.dumpNode(i);
    }

    OP << "qualiArray at the end:\n";
    for (int i = 0; i < nodeFactory.getNumNodes(); i++)
    {
        OP << "num #" << i << ", quali = " << nQualiArray[entry][i] << "\n";
    }
#endif
    std::set<const BasicBlock *> blacklist;
    std::set<const BasicBlock *> whitelist;
    std::set<NodeIndex> visit;
    //OP<<"numNodes = "<<nodeFactory.getNumNodes()<<"\n";
    //2, summarize the update for argument
    //OP<<"summarize the funcs:\n";
    //OP<<"numNodes = "<<nodeFactory.getNumNodes()<<"\n";
    //OP<<"sumNumNodes = "<<fSummary.sumNodeFactory.getNumNodes()<<"\n";
    for (auto &a : F->args())
    {
        Argument *arg = &a;
        NodeIndex argIndex = nodeFactory.getValueNodeFor(arg);
        NodeIndex sumArgIndex = fSummary.sumNodeFactory.getValueNodeFor(arg);
        NodeIndex sumArgObjIndex = fSummary.sumNodeFactory.getObjectNodeFor(arg);
        if (sumArgObjIndex == AndersNodeFactory::InvalidIndex)
            continue;
        //Calculate update for args
        //OP<<"calculate update for arg "<<sumArgIndex<<"\n";
        for (auto sumObj : fSummary.sumPtsGraph[sumArgIndex])
        {
            unsigned sumObjSize = fSummary.sumNodeFactory.getObjectSize(sumObj);
            unsigned sumObjOffset = fSummary.sumNodeFactory.getObjectOffset(sumObj);
            //OP<<"sumObj = "<<sumObj<<", sumObjSize = "<<sumObjSize<<", sumObjOffset = "<<sumObjOffset<<"\n";
            for (auto obj : nPtsGraph[RI][argIndex])
            {
                //OP<<"obj = "<<obj<<"\n";
                unsigned objSize = nodeFactory.getObjectSize(obj);
                unsigned checkSize = std::min(sumObjSize, objSize);
                //OP<<"checkSize = "<<checkSize<<"\n";
                if (obj <= nodeFactory.getConstantIntNode())
                    continue;
                for (unsigned i = 0; i < checkSize; i++)
                {
                    //OP<<"node obj - sumObjOffset + i = "<<obj - sumObjOffset + i<<" : "<<nQualiArray[RI][obj - sumObjOffset + i]<<"\n";
                    //OP<<"entry: "<<nQualiArray[entry].at(obj - sumObjOffset + i)<<"\n";
                    //OP<<"sumArgObjIndex + i = "<<sumArgObjIndex + i<<"\n";
                    fSummary.updateVec.at(sumArgObjIndex + i) = nQualiArray[RI].at(obj - sumObjOffset + i);

                    /*if (nQualiArray[entry].at(obj - sumObjOffset + i) == _UNKNOWN)
                    {
                        fSummary.updateVec.at(sumArgObjIndex + i)= nQualiArray[RI].at(obj - sumObjOffset + i);
                    }
                    else if (nQualiArray[entry][obj - sumObjOffset + i] != nQualiArray[RI].at(obj - sumObjOffset + i))
                    {
                        fSummary.updateVec.at(sumArgObjIndex + i) = nQualiArray[RI].at(obj - sumObjOffset + i);
                    }
                    else
                    {
                        fSummary.updateVec.at(sumArgObjIndex + i) = _UNKNOWN;
                    } */

                    //errs()<<"sumArgObjIndex +i = "<<sumArgObjIndex + i<<"\n";
                    if (fSummary.updateVec.at(sumArgObjIndex + i) == _UNKNOWN)
                    {
                        blacklist.clear();
                        whitelist.clear();
                        visit.clear();
                        //OP<<"obj - sumObjOffset + i = "<<obj - sumObjOffset + i<<"\n";
                        //OP<<"calculate blacklists:\n";
                        calculateRelatedBB(obj - sumObjOffset + i, RI, visit, blacklist, whitelist);
                        //errs()<<"whitelist:\n";
                        for (auto witem : whitelist)
                        {
                            //errs()<<*witem<<"\n";
                            fSummary.args[sumArgObjIndex + i].addToWhiteList(witem->getName().str());
                        }
                        //errs()<<"\nblacklist:\n";
                        for (auto bitem : blacklist)
                        {
                            //errs()<<*bitem<<"\n";
                            fSummary.args[sumArgObjIndex + i].addToBlackList(bitem->getName().str());
                        }
                        //OP<<"calculate relatedNodes for "<<sumArgObjIndex + i<<", obj - sumObjOffset + i = "<<obj - sumObjOffset + i<<"\n";
                        std::set<NodeIndex> relatedSet;
                        for (auto item : relatedNode[obj - sumObjOffset + i])
                        {
                            //OP<<"item = "<<item<<"\n";
                            relatedSet.insert(item);
                            for (auto aa : nAAMap[end][item])
                            {
                                relatedSet.insert(aa);
                                relatedSet.insert(relatedNode[aa].begin(), relatedNode[aa].end());
                            }
                        }

                        for (auto item : relatedSet)
                        {
                            if (item > entryNode)
                                continue;
                            //OP<<"item = "<<item<<"\n";
                            const llvm::Value *val = nodeFactory.getValueForNode(item);
                            int relatedOffset = 0;
                            if (nodeFactory.isObjectNode(item))
                                relatedOffset = nodeFactory.getObjectOffset(item);
                            NodeIndex idx = fSummary.sumNodeFactory.getObjectNodeFor(val);
                            //OP<<"idx = "<<idx<<", relatedOffset = "<<relatedOffset<<"\n";
                            if (idx == AndersNodeFactory::InvalidIndex)
                            {
                                idx = fSummary.sumNodeFactory.getValueNodeFor(val);
                            }
                            if (idx != AndersNodeFactory::InvalidIndex)
                            {
                                fSummary.args[sumArgObjIndex + i].addToRelatedArg(idx + relatedOffset);
                                //OP<<"fSummary.args["<<sumArgObjIndex + i<<"].addToRelatedArg("<<idx+relatedOffset<<")\n";
                            }
                        }
                    }
#ifdef ListProp
                    //copy the list for argument update:
                    if (fSummary.updateVec.at(sumArgObjIndex + i) != _ID)
                    {
                        if (!nodeFactory.listEmpty(obj - sumObjOffset + i))
                        {
                            for (auto item : nodeFactory.getWL(obj - sumObjOffset + i))
                            {
                                fSummary.args[sumArgObjIndex + i].addToWhiteList(item);
                            }
                            for (auto item : nodeFactory.getBL(obj - sumObjOffset + i))
                            {
                                fSummary.args[sumArgObjIndex + i].addToBlackList(item);
                            }
                        }
                    }
#endif
                }
            }
        }
    }
    for (auto item : fSummary.updateVec)
    {
        if (item == _UD)
        {
            uninitOutArg.insert(item);
        }
        else if (item == _UNKNOWN)
        {
            ignoreOutArg.insert(item);
        }
    }
}
void FuncAnalysis::DFS(llvm::Instruction *I, NodeIndex nodeIndex)
{
    std::stack<Instruction *> insStack;
    std::set<Instruction *> visitIns;
    visitIns.clear();
    insStack.push(I);
    //OP<<"inside DFS for "<<*I<<", nodeIndex = "<<nodeIndex<<"\n";
    while (!insStack.empty())
    {
        Instruction *frontIns = insStack.top();
        insStack.pop();
        //OP<<"update inst "<<*frontIns<<"\n";
        //OP<<"update for "<<nodeIndex<<": "<<nQualiArray[frontIns][nodeIndex]<<"\n";
        if (nQualiArray[frontIns].at(nodeIndex) == _UNKNOWN)
            nQualiArray[frontIns].at(nodeIndex) = _ID;

        visitIns.insert(frontIns);
        BasicBlock *BB = frontIns->getParent();

        if (frontIns == &(BB->front()))
        {
            for (auto pi = pred_begin(BB), pe = pred_end(BB); pi != pe; pi++)
            {
                BasicBlock *pred = *pi;
                Instruction *predIns = &pred->back();
                //OP<<"predIns: "<<*predIns;
                if (visitIns.find(predIns) == visitIns.end())
                {
                    //OP<<" : pushed.";
                    insStack.push(predIns);
                }
                //OP<<"\n";
            }
        }
        else
        {
            Instruction *predIns = frontIns->getPrevNode();
            //OP<<"predInst :"<<*predIns;
            if (visitIns.find(predIns) == visitIns.end())
            {
                //OP<<"pushed";
                insStack.push(predIns);
            }
            //OP<<"\n";
        }
    }
}
void FuncAnalysis::setGlobalQualies(std::vector<int> &initArray)
{

    //globalVars|globalVars|FunctionNode|argNode|localVar
    //Set things before argNodes as initialized
    Instruction *entry = &(F->front().front());
    NodeIndex entryNode = nodeFactory.getValueNodeFor(entry);
    bool init = false;
    for (Function::arg_iterator itr = F->arg_begin(), ite = F->arg_end(); itr != ite; ++itr)
    {
        const Argument *arg = &*itr;
        NodeIndex valNode = nodeFactory.getValueNodeFor(arg);

        for (NodeIndex i = 0; i < valNode; i++)
        {
            initArray.at(i) = _ID;
        }
        init = true;
        break;
    }
    //if the function does not own the args
    if (!init)
    {
        for (NodeIndex i = 0; i < entryNode; i++)
        {
            initArray.at(i) = _ID;
        }
    }
    //set the qualifier of FunctionNode
    for (Module::iterator f = M->begin(), fe = M->end(); f != fe; ++f)
    {

        Function *func = &*f;
        if (!func->hasAddressTaken())
            continue;
        NodeIndex fIndex = nodeFactory.getValueNodeFor(func);
        getDef(func);
        std::string fname = getScopeName(func);
        //OP<<"fname = "<<fname<<"\n";
        if (Ctx->FSummaries.find(func) != Ctx->FSummaries.end() && Ctx->FSummaries[func].updateVec.size())
        {
            //OP<<"size of updateVec: "<<Ctx->FSummaries[func].updateVec.size()<<"\n";
            //ret node is the first node (index 0) in the summary
            initArray.at(fIndex) = Ctx->FSummaries[func].updateVec.at(0);
        }
        else
        {
            initArray.at(fIndex) = _ID;
        }
    }
    //set the qualifier of the argument obj and value to _UNKNOWN
    for (Function::arg_iterator itr = F->arg_begin(), ite = F->arg_end(); itr != ite; ++itr)
    {
        const Argument *arg = &*itr;
        //get the value node and set the initArray
        NodeIndex valNode = nodeFactory.getValueNodeFor(arg);
        initArray.at(valNode) = _UNKNOWN;

        NodeIndex objNode = nodeFactory.getObjectNodeFor(arg);
        if (objNode != AndersNodeFactory::InvalidIndex)
        {
            unsigned objSize = nodeFactory.getObjectSize(objNode);
            unsigned objOffset = nodeFactory.getObjectOffset(objNode);
            for (unsigned i = objNode - objOffset; i < objNode - objOffset + objSize; i++)
            {
                initArray.at(i) = _UNKNOWN;
            }
        }
    }
}

bool isEqual(std::vector<int> arr1, std::vector<int> arr2, unsigned len)
{
    for (unsigned i = 0; i < len; i++)
    {
        if (arr1[i] != arr2[i])
            return false;
    }
    return true;
}
void FuncAnalysis::qualiJoin(std::vector<int> &qualiA, std::vector<int> &qualiB, unsigned len)
{
    //OP<<"Inside qualiJoin:\n";
    for (unsigned i = 0; i < len; i++)
    {
        //OP<<"i = "<<i<<", qualiA = "<<qualiA.at(i)<<", qualiB = "<<qualiB.at(i)<<"\n";
        if (qualiA.at(i) == _UD || qualiB.at(i) == _UD)
        {
            qualiA.at(i) = _UD;
        }
        else if (qualiA.at(i) == _UNKNOWN || qualiB.at(i) == _UNKNOWN)
        {
            qualiA.at(i) = _UNKNOWN;
        }
        else
        {
            qualiA.at(i) = std::min(qualiA.at(i), qualiB.at(i));
        }
    }
}
void FuncAnalysis::updateJoin(std::vector<int> &qualiA, std::vector<int> &qualiB, unsigned len)
{
    for (unsigned i = 0; i < len; i++)
    {
        qualiA[i] = std::min(qualiA[i], qualiB[i]);
    }
}

int getQualiForConstant(const ConstantExpr *ce, AndersNodeFactory &nodeFactory, std::vector<int> qualiArray)
{
    switch (ce->getOpcode())
    {
        case Instruction::GetElementPtr:
        {
            if (const ConstantExpr *cexpr = dyn_cast<ConstantExpr>(ce->getOperand(0)))
                return getQualiForConstant(cexpr, nodeFactory, qualiArray);
            NodeIndex baseNode = nodeFactory.getValueNodeFor(ce->getOperand(0));
            //OP<<"baseNode:"<<baseNode<<", quali = "<<qualiArray[baseNode]<<"\n";
            assert(baseNode != AndersNodeFactory::InvalidIndex && "missing base val node for gep");
            return qualiArray[baseNode];
        }
        case Instruction::BitCast:
        case Instruction::PtrToInt:
        case Instruction::IntToPtr:
        {
            NodeIndex srcNode = nodeFactory.getValueNodeFor(ce->getOperand(0));
            if (const ConstantExpr *cexpr = dyn_cast<ConstantExpr>(ce->getOperand(0)))
            {
                return getQualiForConstant(cexpr, nodeFactory, qualiArray);
            }
            return qualiArray[srcNode];
        }
        case Instruction::Sub:
        {
            int qualiA = _ID;
            int qualiB = _ID;
            if (const ConstantExpr *cexpr = dyn_cast<ConstantExpr>(ce->getOperand(0)))
                qualiA = getQualiForConstant(cexpr, nodeFactory, qualiArray);
            else
            {
                NodeIndex op0Index = nodeFactory.getValueNodeFor(ce->getOperand(0));
                qualiA = qualiArray[op0Index];
            }
            if (const ConstantExpr *cexpr = dyn_cast<ConstantExpr>(ce->getOperand(1)))
                qualiB = getQualiForConstant(cexpr, nodeFactory, qualiArray);
            else
            {
                NodeIndex op1Index = nodeFactory.getValueNodeFor(ce->getOperand(0));
                qualiB = qualiArray[op1Index];
            }
            return std::min(qualiA, qualiB);
        }
        default:
            errs() << "Constant Expr not yet handled: " << *ce << "\n";
            return _UD;
            //llvm_unreachable(0);
    }
}
void FuncAnalysis::setReqFor(const llvm::Instruction *I, const llvm::Value *Val, std::vector<int> &out, std::set<const llvm::Value *> &reqVisit)
{
    if (reqVisit.find(Val) != reqVisit.end())
        return;
    reqVisit.insert(Val);
    NodeIndex valNode = nodeFactory.getValueNodeFor(Val);
    for (auto aa : nAAMap[I][valNode])
    {
        if (aa <= nodeFactory.getConstantIntNode() || qualiReq.at(aa) == _ID)
            continue;
        qualiReq.at(aa) = _ID;
        out.at(aa) = _ID;
        //OP<<"aualiReq.at"<<aa<<" = "<<qualiReq.at(aa)<<"\n";

        const llvm::Value *aaVal = nodeFactory.getValueForNode(aa);
        if (!aaVal)
            continue;
        if (const llvm::Instruction *aaIns = dyn_cast<Instruction>(aaVal))
            setReqFor(aaIns, aaVal, out, reqVisit);
    }
    for (auto item : relatedNode[valNode])
    {
        if (item <= nodeFactory.getConstantIntNode() || qualiReq.at(item) == _ID)
            continue;
        qualiReq.at(item) = _ID;
        out.at(item) = _ID;
    }

    if (const Instruction *Inst = dyn_cast<Instruction>(Val))
    {
        if (isa<LoadInst>(Inst))
        {
            NodeIndex srcIndex = nodeFactory.getValueNodeFor(Inst->getOperand(0));
            setReqFor(Inst, Inst->getOperand(0), out, reqVisit);

            for (auto obj : nPtsGraph[I][srcIndex])
            {
                for (auto aa : nAAMap[I][obj])
                {
                    qualiReq.at(aa) = _ID;
                    //out.at(aa) = _ID;
                }
            }
        } //isa<LoadInst>(I)
        for (const Use &U : Inst->operands())
        {
            if (const Instruction *Ins = dyn_cast<Instruction>(U))
            {
                switch (Ins->getOpcode())
                {
                    case Instruction::GetElementPtr:
                    {
                        const GEPOperator *gepValue = dyn_cast<GEPOperator>(Ins);
                        //set requirement for base
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        if (out.at(srcIndex) == _UNKNOWN)
                        {
                            qualiReq.at(srcIndex) = _ID;
                            setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                            out.at(srcIndex) = _ID;
                        }

                        // Make sure all indices are constants
                        for (unsigned i = 1; i < Ins->getNumOperands(); ++i)
                        {
                            if (!isa<ConstantInt>(Ins->getOperand(i)))
                            {
                                NodeIndex offsetIndex = nodeFactory.getValueNodeFor(Ins->getOperand(i));
                                if (out.at(srcIndex) == _UNKNOWN)
                                {
                                    qualiReq.at(srcIndex) = _ID;
                                    setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                                    out.at(srcIndex) = _ID;
                                }
                            }
                        }

                        break;
                    } //case Instruction::GetElementPtr
                    case Instruction::Add:
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
                    case Instruction::ICmp:
                    {
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        NodeIndex op0Index = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        NodeIndex op1Index = nodeFactory.getValueNodeFor(Ins->getOperand(1));
                        if (out.at(op0Index) == _UNKNOWN)
                        {
                            out.at(op0Index) = _ID;
                            qualiReq.at(op0Index) = _ID;
                            setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                        }
                        if (out.at(op1Index) == _UNKNOWN)
                        {
                            out.at(op1Index) = _ID;
                            qualiReq.at(op1Index) = _ID;
                            setReqFor(Ins, Ins->getOperand(1), out, reqVisit);
                        }
                        break;
                    } //case Add
                    case Instruction::SExt:
                    case Instruction::ZExt:
                    case Instruction::BitCast:
                    case Instruction::Trunc:
                    case Instruction::IntToPtr:
                    case Instruction::PtrToInt:
                    {
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        if (out.at(srcIndex) == _UNKNOWN)
                        {
                            out.at(srcIndex) = _ID;
                            qualiReq.at(srcIndex) = _ID;
                            setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                        }
                        break;
                    } //case SExt
                    case Instruction::Load:
                    {
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        //OP<<"Def :"<<*Ins<<" , load from "<<srcIndex<<"\n";
                        for (auto obj : nPtsGraph[Ins][srcIndex])
                        {
                            //OP<<"obj = "<<obj<<"\n";
                            for (auto aa : nAAMap[Ins][obj])
                            {
                                //OP<<"aa = "<<aa<<": "<<nQualiArray[Ins][aa]<<"\n";
                                if (nQualiArray[Ins].at(aa) == _UNKNOWN)
                                {
                                    qualiReq.at(aa) = _ID;
                                    setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                                }
                            }
                        }
                        break;
                    } //case Load
                    case Instruction::PHI:
                    {
                        const PHINode *phiInst = cast<PHINode>(Ins);
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(phiInst);
                        for (unsigned i = 0; i < phiInst->getNumIncomingValues(); i++)
                        {
                            NodeIndex srcIndex = nodeFactory.getValueNodeFor(phiInst->getIncomingValue(i));
                            if (out.at(srcIndex) == _UNKNOWN)
                            {
                                qualiReq.at(srcIndex) = _ID;
                                setReqFor(Ins, phiInst->getIncomingValue(i), out, reqVisit);
                                out.at(srcIndex) = _ID;
                            }
                        }
                        break;
                    } //case PHI
                    case Instruction::Select:
                    {
                        NodeIndex conditionIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        NodeIndex srcIndex1 = nodeFactory.getValueNodeFor(Ins->getOperand(1));
                        NodeIndex srcIndex2 = nodeFactory.getValueNodeFor(Ins->getOperand(2));
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        if (out.at(conditionIndex) == _UNKNOWN)
                        {
                            out.at(conditionIndex) = _ID;
                            qualiReq.at(conditionIndex) = _ID;
                            setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                        }
                        if (out.at(srcIndex1) == _UNKNOWN)
                        {
                            out.at(srcIndex1) = _ID;
                            qualiReq.at(srcIndex1) = _ID;
                            setReqFor(Ins, Ins->getOperand(1), out, reqVisit);
                        }
                        if (out.at(srcIndex2) == _UNKNOWN)
                        {
                            out.at(srcIndex2) = _ID;
                            qualiReq.at(srcIndex2) = _ID;
                            setReqFor(Ins, Ins->getOperand(2), out, reqVisit);
                        }
                        break;
                    } //case Select
                    case Instruction::ExtractValue:
                    {
                        NodeIndex srcIndex = nodeFactory.getValueNodeFor(Ins->getOperand(0));
                        NodeIndex dstIndex = nodeFactory.getValueNodeFor(Ins);
                        if (out[srcIndex] == _UNKNOWN)
                        {
                            out.at(srcIndex) = _ID;
                            qualiReq.at(srcIndex) = _ID;
                            setReqFor(Ins, Ins->getOperand(0), out, reqVisit);
                        }
                        break;
                    } //case ExtractValue
                    case Instruction::Br:
                    {
                        const BranchInst *brInst = cast<BranchInst>(Ins);
                        if (I->getNumOperands() == 3)
                        {
                            NodeIndex condIndex = nodeFactory.getValueNodeFor(brInst->getCondition());
                            if (out.at(condIndex) == _UNKNOWN)
                            {
                                out.at(condIndex) = _ID;
                                qualiReq.at(condIndex) = _ID;
                                setReqFor(Ins, brInst->getCondition(), out, reqVisit);
                            }
                        }
                        break;
                    } //case Br
                    default:
                    {
                        return;
                    }

                } //switch (Ins->getOpcode())
            }     //if (Instruction *Ins = dyn_cast<Instruction>(U))
        }         //for (Use &U : I->operands())
    }
}