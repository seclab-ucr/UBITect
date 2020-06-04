#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/CFG.h"
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

using namespace llvm;
void FuncAnalysis::processInitFuncs (Instruction *I, llvm::Function* Callee, bool init, std::vector<int> &in, std::vector<int> &out)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    Value *dst = CI->getArgOperand(0);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(dst);
    int qualiSrc = _ID;
    std::set<const llvm::Value*> reqVisit;
    if (out.at(dstIndex) == _UNKNOWN)
    {
	if (dstIndex>nodeFactory.getConstantIntNode())
            setReqFor(I, dst, out, reqVisit);
	out.at(dstIndex) = _ID;
    }
    if (out.at(dstIndex) == _UD)
	qualiSrc = _UD;

    if (Callee->getName().str() == "llvm.va_start")
    {
    	for (auto obj : nPtsGraph[I][dstIndex])
	{
		if (obj <= nodeFactory.getConstantIntNode())
			continue;
		int objSize = nodeFactory.getObjectSize(obj);
		for (int i = 0; i < objSize; i++)
			out.at(obj+i) = qualiSrc;
	}
	return;
    }

    Value *src = CI->getArgOperand(1);
    Value *size = CI->getArgOperand(2);
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(src);
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(size);
    //0.set the qualifer req for args
    if (out.at(srcIndex) == _UNKNOWN)
    {
	if (srcIndex>nodeFactory.getConstantIntNode())
            setReqFor(I, src, out, reqVisit);
	out.at(srcIndex) = _ID;
    }
    if (out.at(sizeIndex) == _UNKNOWN)
    {
	if (sizeIndex > nodeFactory.getConstantIntNode())
	    setReqFor(I, size, out, reqVisit);
        out.at(sizeIndex) = _ID;
    }
    qualiSrc = _ID;
   //1. set the qualifier of target to initialized
    if (out.at(srcIndex) == _UD || out.at(sizeIndex) == _UD)
    {
        qualiSrc = _UD;
    }
    //look the real type for memset.
    const Type *type = cast<PointerType>(dst->getType())->getElementType();
    while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
        type = arrayType->getElementType();
    // Now construct the pointer and memory object variable
    // It depends on whether the type of this variable is a struct or not
    if (const StructType *structType = dyn_cast<StructType>(type))
    {
        const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(structType, M);
        uint64_t stSize = stInfo->getExpandedSize();
        for (auto obj: nPtsGraph[I][dstIndex])
        {
            for (int i = 0; i < stSize; i++)
            {
                out.at(obj + i) = qualiSrc;
            }
        }
    }
    else
    {
        for (auto obj: nPtsGraph[I][dstIndex])
        {
	    if (obj <= nodeFactory.getConstantIntNode())
		continue;
            out.at(obj) = qualiSrc;
        }
    }
}
void FuncAnalysis::processCopyFuncs (Instruction *I, llvm::Function* Callee, bool init, std::vector<int> &in, std::vector<int> &out)
{
    unsigned numNodes = nodeFactory.getNumNodes();
    CallInst *CI = dyn_cast<CallInst>(I);
    if(CI->getNumArgOperands() < 3)
        return;
    std::set<const llvm::Value*> reqVisit;

    Value *dst = CI->getArgOperand(0);
    Value *src = CI->getArgOperand(1);
    Value *size = CI->getArgOperand(2);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(dst);
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(src);
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(size);
   
    //0.set the qualifer req for args
    if (out.at(srcIndex) == _UNKNOWN)
    {
        setReqFor(I, src, out, reqVisit);
	out.at(srcIndex) = _ID;
    }
    if (out.at(dstIndex) == _UNKNOWN)
    {
        setReqFor(I, dst, out, reqVisit);
	out.at(dstIndex) = _ID;
    }
    if (out.at(sizeIndex) == _UNKNOWN)
    {
        setReqFor(I, size, out, reqVisit);
	out.at(sizeIndex) = _ID;
    }
    if(!dst->getType()->isPointerTy() || !src->getType()->isPointerTy())
        return;
    
    if (out.at(srcIndex) == _UD || out.at(sizeIndex) == _UD)
    {
        out.at(dstIndex) = _UD;
        return;
    }
    uint64_t objSize = 0;
    //1. If we copy an arg node to a heap pbj or an unknown pointer obj, 
    //we need to set the requirement for arg
    for (auto obj : nPtsGraph[I][dstIndex])
    {   
        //copy to the heap
        if (obj < nodeFactory.getNullPtrNode() || nodeFactory.isHeapNode(obj))
        {   
            for (auto srcObj : nPtsGraph[I][srcIndex])
            {
                if (srcObj <= nodeFactory.getConstantIntNode())
                    continue;
                unsigned srcObjOffset = nodeFactory.getObjectOffset(srcObj);
                unsigned srcObjSize = nodeFactory.getObjectSize(srcObj);
                for (unsigned i = srcObjOffset; i < srcObjSize-srcObjOffset; i++)
                {
                    if (nQualiArray[I].at(srcObj + i) == _UNKNOWN)
                    {
			qualiReq.at(srcObj+i) = _ID;
                        out.at(srcObj + i) = _ID;
                        //DFS (I, srcObj + i);
                    }
                }
            }
        }
	if (nodeFactory.isArgNode(obj)) {
	    for (auto srcObj : nPtsGraph[I][srcIndex]) {
		if (srcObj <= nodeFactory.getConstantIntNode())
			continue;
		unsigned srcObjOffset = nodeFactory.getObjectOffset(srcObj);
		unsigned srcObjSize = nodeFactory.getObjectSize(srcObj);
		for (unsigned i = srcObjOffset; i < srcObjSize-srcObjOffset; i++) {
		    if (in.at(srcObj + i) == _UNKNOWN)
		    {
			relatedNode[obj+i].insert(srcObj+i);
			relatedNode[obj+i].insert(relatedNode[srcObj+i].begin(), relatedNode[srcObj+i].end());
		    }
		}
	    }
	}
    }
    //2. Identify the object size to be copied.
    for (auto obj : nPtsGraph[I][dstIndex])
    {
        if (obj <= nodeFactory.getConstantIntNode())
            continue;
	if (objSize > 0)
        	objSize = ((objSize < nodeFactory.getObjectSize(obj))? objSize : nodeFactory.getObjectSize(obj));
	else
		objSize = nodeFactory.getObjectSize(obj);
	if(nodeFactory.isUnionObjectNode(obj))
	{
		objSize = 1;
		break;
	}
        //copy from middle, the field pointer.
        if (objSize>nodeFactory.getObjectOffset(obj) && nodeFactory.getObjectOffset(obj) != 0)
        {
            objSize = nodeFactory.getObjectSize(obj) - nodeFactory.getObjectOffset(obj);
        }
    }
    for (auto srcObj : nPtsGraph[I][srcIndex])
    {
	if(srcObj <= nodeFactory.getConstantIntNode())
		continue;
  	if(nodeFactory.isUnionObjectNode(srcObj))
        {
                objSize = 1;
                break;
        }
	unsigned srcObjOffset = nodeFactory.getObjectOffset(srcObj);
	 objSize = ((objSize < nodeFactory.getObjectSize(srcObj)-srcObjOffset)? objSize : nodeFactory.getObjectSize(srcObj)-srcObjOffset);
    }
    //consider casting to i8* before copy, this case may be included into the previous calculate the object size case.
    if (BitCastInst *BCI = dyn_cast<BitCastInst>(src))
    {
        const Type *type = cast<PointerType>(I->getOperand(0)->getType())->getElementType();

        while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
            type = arrayType->getElementType();
        if (const StructType *structType = dyn_cast<StructType>(type))
        {
            if (!structType->isOpaque())
            {
                const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(structType, F->getParent());
                objSize = stInfo->getExpandedSize();
            }
	    if(!structType->isLiteral() && structType->getStructName().startswith("union"))
		objSize = 1;
        }
    }
    if (out.at(dstIndex) == _ID)
    { 
        // Now construct the pointer and memory object variable
        // It depends on whether the type of this variable is a struct or not
        bool init = false;
        for(auto obj : nPtsGraph[I][dstIndex])
        {
            //unsigned objSize = nodeFactory.getObjectSize(obj);
            //considering memcpy to universal ptr node
	    // OP<<"obj = "<<obj<<"\n";
	    if(obj<=nodeFactory.getConstantIntNode())
		continue;
            for(auto srcObj : nPtsGraph[I][srcIndex])
            {
                if (obj < nodeFactory.getNullPtrNode())
                {
                    if (out.at(srcObj) == _UNKNOWN)
                    {
                        qualiReq[srcObj] = _ID;
			out.at(srcObj) = _ID;
                        //DFS(I, srcObj);
                    } 
                }
                //unsigned objSize = nodeFactory.getObjectSize(srcObj);
                for (int i = 0; i < objSize; i++)
                {
		  // OP<<"srcObj+i ="<<srcObj+i<<"\n"; 
                    //considering memcpy from universal ptr node
                    int srcQuali = 0;
                    if (srcObj <= nodeFactory.getConstantIntNode())
                    {
                        srcQuali = _ID;
                    }
                    else{
                        srcQuali = out.at(srcObj + i);
			if (srcQuali == _UNKNOWN) {
			    relatedNode[obj+i].insert(srcObj+i);
			    for (auto aa : nAAMap[I][srcObj]){
			    	relatedNode[obj+i].insert(relatedNode[aa].begin(), relatedNode[aa].end());
			    }
			#ifdef _RELATED
			    OP<<"related node for "<<obj+i<<"\n";
			    for (auto item : relatedNode[obj+i])
				OP<<item<<"/";
			    OP<<"\n";
			#endif
			}
                    }
		    if (obj + i >= numNodes)
			break;
          //         OP<<"obj + i = "<<obj + i<<"srcObj + i = "<<srcObj + i<<", srcQuali = "<<srcQuali<<"\n";
                    if (!init || srcQuali == _ID)
                    {
                        out.at(obj + i) = srcQuali;
                        init = true;
                    }
                    else{
                        out.at(obj + i) = std::min(out.at(obj + i), srcQuali);
                    }
                }

            }
        }
    }
}
void FuncAnalysis::processTransferFuncs (Instruction *I, llvm::Function* Callee, bool init, std::vector<int> &in, std::vector<int> &out)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    //1. copy the qualifier inference from src to dst
    Value *dst = CI->getArgOperand(0);
    Value *src = CI->getArgOperand(1);
    Value *size = CI->getArgOperand(2);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(dst);
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(src);
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(size);
    std::set<const llvm::Value*> reqVisit;
    //0.set the qualifer req for args
    if (out.at(srcIndex) == _UNKNOWN)
    {
        out.at(srcIndex) = _ID;
        setReqFor(I, src, out, reqVisit);
    }
    if (out.at(dstIndex) == _UNKNOWN)
    {
        out.at(dstIndex) = _ID;
        setReqFor(I, dst, out, reqVisit);
    }
    if (out.at(sizeIndex) == _UNKNOWN)
    {
        out.at(sizeIndex) = _ID;
        setReqFor(I, size, out, reqVisit);
    }
    
    const Type *type = cast<PointerType>(dst->getType())->getElementType();
    while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
        type = arrayType->getElementType();


    //1. copy the data from src to dst
    if (out.at(srcIndex) != _ID || out.at(sizeIndex) != _ID)
    {
        out.at(dstIndex) = _UD;
        return;
    }
    if (out.at(dstIndex) == _ID)
    {
        bool init = false;
        // Now construct the pointer and memory object variable
        // It depends on whether the type of this variable is a struct or not
        if (const StructType *structType = dyn_cast<StructType>(type))
        {
            const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(structType, M);
            uint64_t stSize = stInfo->getExpandedSize();
            for (auto obj: nPtsGraph[I][dstIndex])
            {
                for(auto srcObj : nPtsGraph[I][srcIndex])
                {
                    for (int i = 0; i < stSize; i++)
                    {
                        if (out.at(srcObj + i) == _UNKNOWN)
                        {
			    qualiReq.at(srcObj + i) = _ID;
                            out.at(srcObj + i) = _ID;
                        }
                        int srcQuali = 0;
                        if (srcObj <= nodeFactory.getConstantIntNode())
                        {
                            srcQuali = _ID;
                        }
                        else{
                            srcQuali = in[srcObj + i];
                        }
                        if (!init || srcQuali == _UD)
                        {
                            out.at(obj + i) = srcQuali;
                            init = true;
                        }
                        else{
                            out.at(obj + i) = std::min(out.at(obj + i),srcQuali);
                        }
                    }
                }
            }
        }
        else
        {
            for (auto obj: nPtsGraph[I][dstIndex])
            {
                for (auto srcObj : nPtsGraph[I][srcIndex])
                {
                    if (out.at(srcObj) == _UNKNOWN)
                    {
			reqVisit.clear();
                        setReqFor(I, src, out, reqVisit);
			out.at(srcObj) = _ID;
                    }
                    int srcQuali = 0;
                    if (srcObj <= nodeFactory.getConstantIntNode())
                    {
                        srcQuali = _ID;
                    }
                    else{
                        srcQuali = in[srcObj];
                    }
                    if (!init || srcQuali == _UD)
                    {
                        out.at(obj) = srcQuali;
                        init = true;
                    }
                    else
                    {
                        out.at(obj) = std::min(out.at(obj), srcQuali);
                    }
                }
            }
        }
    }
}
void FuncAnalysis::processFuncs (llvm::Instruction *I, llvm::Function* Callee, bool init, std::vector<int>& in,std::vector<int>& out)
{
    //only update the arguments and the return value from Callees, req propagation is done later in summarizeFuncs().   
#ifdef PRINT_SUMF 
    OP<<"Functions in Ctx->FSummaries: \n";
    for (auto item : Ctx->FSummaries)
    {
	OP<<"--Addr : "<<item.first<<", name: "<<item.first->getName().str()<<"\n";
    }
#endif
    if (Callee->empty()) {
		auto FIter = Ctx->Funcs.find(Callee->getName().str());
		if (FIter != Ctx->Funcs.end()) {
			Callee = FIter->second;
    	}
    }
    if(Callee == NULL || Ctx->FSummaries.find(Callee) == Ctx->FSummaries.end()){
        return ;
    }
    std::set<const llvm::Value*> reqVisit;
    //Insert the callee's related BC to the caller
    #ifdef _LINK
    for (auto item: Ctx->FSummaries[Callee].relatedBC) {
	fSummary.relatedBC.insert(item);
    }
    #endif
    CallInst *CI = dyn_cast<CallInst>(I);
    std::vector<const Argument *> calleeArgs;
    for (Function::arg_iterator itr = Callee->arg_begin(), ite = Callee->arg_end(); itr != ite; ++itr)
    {

        const Argument *arg = &*itr;
        calleeArgs.push_back(arg);
    }
    int sumNumNodes = Ctx->FSummaries[Callee].noNodes;
    //for (int i = 0; i < sumNumNodes; i++)
    //update the argument and propagate the requirement
    for (int argNo = 0; argNo < CI->getNumArgOperands(); argNo++)
    {
        NodeIndex argNode = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
	//Deal with VarArg function
        if (argNo >= calleeArgs.size())
        {  
            if (out.at(argNode) == _UNKNOWN)
            {   
                out.at(argNode) = _ID;
		reqVisit.clear();
                setReqFor(I, CI->getArgOperand(argNo), out, reqVisit);
            }
            for (auto obj : nPtsGraph[I][argNode])
            {
                if (obj <= nodeFactory.getConstantIntNode())
                    continue;
                unsigned objSize = nodeFactory.getObjectSize(obj);
                unsigned objOffset = nodeFactory.getObjectOffset(obj);
                for (unsigned i = 0; i < objSize; i++)
                {
                    if (nQualiArray[I].at(obj - objOffset + i) == _UNKNOWN)
                    {   
                        out.at(obj - objOffset + i) = _ID;
                        //DFS(I, obj - objOffset + i);
                    }
                }
            }
            continue;
        }
	
        NodeIndex sumArgNode = Ctx->FSummaries[Callee].args[argNo + 1].getNodeIndex();;
	//Check the pointer itself
	if (Ctx->FSummaries[Callee].reqVec.at(sumArgNode) == _ID)
        {
            if (out.at(argNode) == _UNKNOWN)
            {
                //out.at(argNode) = _ID;
		reqVisit.clear();
                setReqFor(I, CI->getArgOperand(argNo), out, reqVisit);
            }
        }
        //Ctx->FSummaries[Callee].summary();
	unsigned numNodes = nodeFactory.getNumNodes();
        for (auto sumObj : Ctx->FSummaries[Callee].sumPtsGraph[sumArgNode])
        {
            unsigned sumObjSize = Ctx->FSummaries[Callee].args[argNo].getObjSize();
            unsigned sumObjOffset = Ctx->FSummaries[Callee].args[argNo].getOffset();
            for (auto obj : nPtsGraph[I][argNode])
            {
                if (obj <= nodeFactory.getConstantIntNode())
                    continue;
		//Deal with the union object 
		unsigned objSize = nodeFactory.getObjectSize(obj);
		unsigned objOffset = nodeFactory.getObjectOffset(obj);
		unsigned checkSize = std::min(objSize-objOffset, sumObjSize-sumObjOffset);
		if (nodeFactory.isUnionObjectNode(obj))
		{
			bool init = false;
			for (unsigned i = 0; i < checkSize; i++)
	                {
			   
             	           if (Ctx->FSummaries[Callee].updateVec[sumObj + i] != _UNKNOWN){
				if (!init) {	
				    if (out.at(obj) >= Ctx->FSummaries[Callee].reqVec[sumObj + i]){
				        out.at(obj) = Ctx->FSummaries[Callee].updateVec[sumObj + i];
				        init = true;
				    }
			   	}else{
				    if (out.at(obj) >= Ctx->FSummaries[Callee].reqVec[sumObj + i]) {
                          	        out.at(obj) = std::min( out.at(obj), Ctx->FSummaries[Callee].updateVec[sumObj + i]);
				    }
				}
			   }
			#ifdef ML_MODE
			   else{
				nodeFactory.setWL(obj, Ctx->FSummaries[Callee].args[sumObj+i].getWhiteList());
	                        nodeFactory.setBL(obj, Ctx->FSummaries[Callee].args[sumObj+i].getBlackList());

			   }
			#endif
               		 }
		}
		else
    	        {			
                //update the arg->obj from the offset till end
                for (unsigned i = 0; i < checkSize; i++)
                {
		    if(obj + i >= numNodes)	
        		break;            
                    if (Ctx->FSummaries[Callee].updateVec[sumObj + i] != _UNKNOWN)
		    {
			if (out.at(obj+i) >= Ctx->FSummaries[Callee].reqVec[sumObj + i]) {
                            out.at(obj + i) = Ctx->FSummaries[Callee].updateVec[sumObj + i];
			}
		    }
		    else  {
			#ifdef ML_MODE
			nodeFactory.setWL(obj + i, Ctx->FSummaries[Callee].args[sumObj+i].getWhiteList());
                        nodeFactory.setBL(obj + i, Ctx->FSummaries[Callee].args[sumObj+i].getBlackList());
			#endif
			std::set<NodeIndex> sumRSet = Ctx->FSummaries[Callee].args[sumObj+i].getRelatedArgs();
			if (sumRSet.empty())
			    continue;
			bool init = false;
			for (auto sumRitem : sumRSet) {
			    int argNoCurr = Ctx->FSummaries[Callee].args[sumRitem].getNodeArgNo();
			    NodeIndex argNoIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(argNoCurr));	    
			    if (argNoIndex == AndersNodeFactory::InvalidIndex){
				continue;
			    }
			    if (nodeFactory.isObjectNode(argNoIndex) && nodeFactory.getObjectSize(argNoIndex) < i)
				continue;
			    if (argNoIndex +i >= nodeFactory.getNumNodes())
				continue;
			    if (out.at(argNoIndex + i) == _UNKNOWN) {
				relatedNode[obj+i].insert(relatedNode[argNoIndex + i].begin(), relatedNode[argNoIndex + i].end());
			    }
			    if (!init) {
				out.at(obj + i) = out.at(argNoIndex + i);
				init = true;
			    }
			    else {
				out.at(obj + i) = std::min(out.at(obj + i), out.at(argNoIndex + i));
			    }
			}
		    }
                }
		}
                //update the rest object if arg point to the middle of the obj
                //unsigned objOffset = nodeFactory.getObjectOffset(obj);
                if (sumObjOffset > 0 && objOffset > 0)
                {
                    if (sumObjOffset < objOffset)
                        continue;
                     
                    //unsigned objSize = nodeFactory.getObjectSize(obj);
                    for (unsigned i = objOffset; i > 0; i--)
                    {
                        if (Ctx->FSummaries[Callee].updateVec[sumObj - i] != _UNKNOWN)
                        {
			    if (out.at(obj-i) >= Ctx->FSummaries[Callee].reqVec[sumObj - i]) {
                                out.at(obj - i) = Ctx->FSummaries[Callee].updateVec[sumObj - i];
			    }
                        }
			#ifdef ML_MODE
			else {
				nodeFactory.setWL(obj - i, Ctx->FSummaries[Callee].args[sumObj-i].getWhiteList());
                       		nodeFactory.setBL(obj - i, Ctx->FSummaries[Callee].args[sumObj-i].getBlackList());
			}
			#endif
                    }
                }
            }

        }
    }
    //update the return value and object
    if (I->getType()->isVoidTy())
    {
        return;
    }
    NodeIndex retNode = nodeFactory.getValueNodeFor(I);
    NodeIndex sumRetNode = Ctx->FSummaries[Callee].getRetNodes();
    out.at(retNode) = Ctx->FSummaries[Callee].updateVec[sumRetNode];
    //context-sensitivity	
    std::set<NodeIndex> sumRSet = Ctx->FSummaries[Callee].args[sumRetNode].getRelatedArgs();
    //Ctx->FSummaries[Callee].summary();
    if (!sumRSet.empty()) {
        bool init = false;
        for (auto sumRitem : sumRSet) {
    	    int argNoCurr = Ctx->FSummaries[Callee].args[sumRitem].getNodeArgNo();
	    if (isa<Function>(CI->getArgOperand(argNoCurr)))
		continue;
	    NodeIndex argNoIndex = nodeFactory.getObjectNodeFor(CI->getArgOperand(argNoCurr));
	    int argOffset = Ctx->FSummaries[Callee].args[sumRitem].getOffset();
            if (argNoIndex == AndersNodeFactory::InvalidIndex && argOffset == 0){
	        argNoIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(argNoCurr));
	    }
	    if (argNoIndex == AndersNodeFactory::InvalidIndex)
		continue;
            if (out.at(argNoIndex + argOffset) == _UNKNOWN) {
                relatedNode[retNode].insert(relatedNode[argNoIndex + argOffset].begin(), relatedNode[argNoIndex + argOffset].end());
            }
            if (!init) {
                out.at(retNode) = out.at(argNoIndex + argOffset);
                init = true;
            }
            else {
            	out.at(retNode) = std::min(out.at(retNode), out.at(argNoIndex + argOffset));
            }
        }
     }



    for (auto sumRetObj : Ctx->FSummaries[Callee].sumPtsGraph[sumRetNode])
    {
	unsigned sumRetSize = Ctx->FSummaries[Callee].getRetSize();
        unsigned sumRetOffset = Ctx->FSummaries[Callee].getRetOffset();
	
        for (auto retObj : nPtsGraph[I][retNode])
        {
            if(retObj <= nodeFactory.getConstantIntNode())
                continue;
	    unsigned retObjSize = nodeFactory.getObjectSize(retObj);
	    unsigned retObjOffset = nodeFactory.getObjectOffset(retObj);
	    unsigned checkSize = std::min(sumRetSize - sumRetOffset, retObjSize - retObjOffset);
            for (unsigned i = 0; i < checkSize; i++)
            {
                if (Ctx->FSummaries[Callee].updateVec[sumRetObj + i] != _UNKNOWN){
                    out.at(retObj + i) = Ctx->FSummaries[Callee].updateVec[sumRetObj + i];
		    if (Ctx->FSummaries[Callee].args[sumRetObj+i].getMayNull()) {
			nodeFactory.setMayNull(sumRetObj+i);
		    }
		}
		else  {
                        std::set<NodeIndex> sumRSet = Ctx->FSummaries[Callee].args[sumRetObj+i].getRelatedArgs();
                        if (sumRSet.empty())
                            continue;
                        bool init = false;
                        for (auto sumRitem : sumRSet) {
                            int argNoCurr = Ctx->FSummaries[Callee].args[sumRitem].getNodeArgNo();
                            NodeIndex argNoIndex = nodeFactory.getObjectNodeFor(CI->getArgOperand(argNoCurr));
                            if (argNoIndex == AndersNodeFactory::InvalidIndex)
                                continue;
                            if (out.at(argNoIndex + i) == _UNKNOWN) {
                                relatedNode[retObj+i].insert(relatedNode[argNoIndex + i].begin(), relatedNode[argNoIndex + i].end());
                            }
                            if (!init) {
                                out.at(retObj + i) = out.at(argNoIndex + i);
                                init = true;
                            }
                            else {
                                out.at(retObj + i) = std::min(out.at(retObj + i), out.at(argNoIndex + i));
                            }
                        }
                    }	
            }
        }
    }
}
void FuncAnalysis::checkCopyFuncs(llvm::Instruction *I, llvm::Function *Callee)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    std::string warningTy = "OTHER";
    if(CI->getNumArgOperands() < 3)
        return;
    std::set<const Instruction*> visit;
    Value *dst = CI->getArgOperand(0);
    Value *src = CI->getArgOperand(1);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(0));
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(1));
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(2));
    if(!dst->getType()->isPointerTy() || !src->getType()->isPointerTy())
        return;
    if (nQualiArray[I].at(dstIndex) != _ID) {
    	insertUninit(I, dstIndex, uninitArg);
    }

    if (nQualiArray[I].at(dstIndex) == _UD)
    {
	if (!warningReported(I, dstIndex))
	{
	    #ifdef PRINTWARN
            OP<<"***********Warning: argument check fails @ argument 0: dst pointer not initialized\n";
            OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
	    #endif
            visit.clear();
	    warningTy = warningTy = eToS[getWType(I->getOperand(0)->getType())];
            printRelatedBB(dstIndex, I, visit, warningTy, 0);
	    warningSet.insert(dstIndex);
	}
    }
    if (nQualiArray[I].at(srcIndex) != _ID) {
        insertUninit(I, srcIndex, uninitArg);
    }

    if (nQualiArray[I].at(srcIndex) == _UD)
    {
	if(!warningReported(I, srcIndex))
	{
	    insertUninit(I, srcIndex, uninitArg);
	    #ifdef PRINTWARN
            OP<<"***********Warning: argument check fails @ argument 1: src pointer not initialized\n";
            OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
	    #endif
            visit.clear();
	    warningTy = eToS[getWType(I->getOperand(1)->getType())];
            printRelatedBB(srcIndex, I, visit, warningTy, 1);
	    warningSet.insert(srcIndex);
	}
    }
    //check the src object, if the dst obj is heap node then the qualifier should be initialized:
    for (auto dstObj : nPtsGraph[I][dstIndex])
    {
	if (dstObj < nodeFactory.getNullPtrNode() || nodeFactory.isHeapNode(dstObj))
	{
		for (auto obj : nPtsGraph[I][srcIndex])
    		{
        		if (obj <= nodeFactory.getConstantIntNode())
            			continue;
        		unsigned objSize = nodeFactory.getObjectSize(obj);
        		//copy from middle, the field pointer.
        		if (nodeFactory.getObjectOffset(obj) != 0)
        		{
            			objSize = objSize - nodeFactory.getObjectOffset(obj);
        		}
        		for (int i = 0; i < objSize; i++)
        		{
				if (nQualiArray[I].at(obj + i) != _ID)
				{
				    insertUninit(I, obj+i, uninitArg);
				}		
            			if (nQualiArray[I].at(obj + i) == _UD)
            			{
					if (warningReported(I, obj + i))
						continue;
					#ifdef PRINTWARN
                			OP<<"***********Warning: argument check fails @ argument 1: field"<<i<<" not initialized\n";
                			OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
                			OP<<"obj + i = "<<obj + i <<", qualifier ="<<nQualiArray[I].at(obj+i)<<"\n";
                			#endif
					visit.clear();
                			printRelatedBB(obj+i, I, visit, "DATA", 1, i);
					warningSet.insert(obj + i);
            			}
        		}

    		}
	}
	else {
	}
    }

    if (nQualiArray[I].at(sizeIndex) == _UD)
    {
	if (nQualiArray[I].at(sizeIndex) != _ID) {
		insertUninit(I, sizeIndex, uninitArg);
	}
	if (!warningReported(I, sizeIndex))
	{
	    #ifdef PRINTWARN
            OP<<"***********Warning: argument check fails @ argument 3: size not initialized\n";
            OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
	    #endif
            visit.clear();
            printRelatedBB(sizeIndex, I, visit, "DATA", 3);
	    warningSet.insert(sizeIndex);
	}
    }
}
void FuncAnalysis::checkTransferFuncs(llvm::Instruction *I, llvm::Function *Callee)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(0));
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(1));
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(CI->getArgOperand(2));
    std::set<const Instruction*> visit;
    std::string warningTy = "OTHER";
    if (nQualiArray[I].at(srcIndex) == _UD)
    {	
	if (nQualiArray[I].at(srcIndex) == _UD) {
                insertUninit(I, srcIndex, uninitArg);
        }

	if (!warningReported(I, srcIndex))
	{
	    #ifdef PRINTWARN
            OP<<"***********Arg Warning: argument check fails @ argument 1: src pointer not initialized\n";
            OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
	    #endif
            visit.clear();
	    warningTy = eToS[getWType(I->getOperand(0)->getType())];
            printRelatedBB(srcIndex, I, visit, warningTy,1);
	    warningSet.insert(srcIndex);
	}
    }

    const Type *type = cast<PointerType>(CI->getArgOperand(1)->getType())->getElementType();
    if (const StructType *structType = dyn_cast<StructType>(type))
    {
        if (!structType->isOpaque()){
            const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(structType, M);
            uint64_t stSize = stInfo->getExpandedSize();
            for (auto obj : nPtsGraph[I][srcIndex])
            {
                for (int i = 0; i < stSize; i++)
                {
                    if (nQualiArray[I].at(obj + i) == _UD)
                    {
		        insertUninit(I, obj+i, uninitArg);

			if (warningReported(I, obj+i))
			    continue;
			#ifdef PRINTWARN
                        OP<<"***********Warning: argument check fails @ argument 1: field"<<i<<" not initialized\n";
                        OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
			#endif
                        visit.clear();
			warningTy = eToS[getWType(I->getOperand(1)->getType())];
                        printRelatedBB(obj+i, I, visit, warningTy, 1, i);
			warningSet.insert(obj+i);
                    }
                }
            } 
        
        }    
    }
    else{
        for (auto obj : nPtsGraph[I][srcIndex])
        {
            if (nQualiArray[I].at(obj) == _UD)
            {
                insertUninit(I, obj, uninitArg);

		if (warningReported(I, obj))
		    continue;
		#ifdef PRINTWARN
                OP<<"***********Warning: argument check fails @ argument 1: data not initialized\n";
                OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
		#endif
                visit.clear();
                printRelatedBB(srcIndex, I, visit, "DATA", 1);
		warningSet.insert(srcIndex);
            }
        }    
    }
    if (nQualiArray[I].at(sizeIndex) != _ID) {
    	insertUninit(I, sizeIndex, uninitArg);
    }

    if (nQualiArray[I].at(sizeIndex) == _UD)
    {
	if (!warningReported(I, sizeIndex))
	{
		#ifdef PRINTWARN
        	OP<<"***********Warning: argument check fails @ argument 3: size not initialized\n";
        	OP<<"[trace] In function @"<<Callee->getName().str()<<" Instruction:"<<*I<<"\n";
		#endif
        	visit.clear();
        	printRelatedBB(sizeIndex, I, visit, "DATA", 3);
		warningSet.insert(sizeIndex);
	}
    }
}
void FuncAnalysis::checkFuncs(llvm::Instruction *I, llvm::Function *Callee)
{
    #ifdef PRINT_CURRENT_SUM
    OP<<"current set of fsum:\n";
    for (auto sum : Ctx->FSummaries)
    {
        OP<<sum.first<<": "<<sum.first->getName().str()<<"\n";
    }
    #endif
    if (Callee->empty()) {
	auto FIter = Ctx->Funcs.find(Callee->getName().str());
        if (FIter != Ctx->Funcs.end()) {
		Callee = FIter->second;
        }
    }
    if(Ctx->FSummaries.find(Callee) == Ctx->FSummaries.end())
    {
        return;
    }
    //Ctx->FSummaries[Callee].summary();
    CallInst *CI = dyn_cast<CallInst>(I);
    Instruction *entry = &(F->front().front());
    NodeIndex entryIndex = nodeFactory.getValueNodeFor(entry);
    std::set<const Instruction*> visit;
    int argNums = CI->getNumArgOperands();
    std::vector<const Argument *> calleeArgs;
    std::string warningTy = eToS[OTHER];

    for (Function::arg_iterator itr = Callee->arg_begin(), ite = Callee->arg_end(); itr != ite; ++itr)
    {
        const Argument *arg = &*itr;
        calleeArgs.push_back(arg);
    }
    for (int argNo = 0; argNo < argNums; argNo++)
    {
        //for var arg functions, check the rest of the argument to be init
        if (argNo >= calleeArgs.size())
        {  
            NodeIndex argNode = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
            if (nQualiArray[I].at(argNode) == _UD)
            {   
                insertUninit(I, argNode, uninitArg);
		if (!warningReported(I, argNode))
		{
		    #ifdef PRINTWARN
                    OP<<"***********Warning: argument check fails @ argument "<<argNo<<" : ptr not initialized, Node "<<argNode<<", actual qualifier = "<<nQualiArray[I].at(argNode)<<"\n";
                    OP<<"[trace] In function @"<<F->getName().str()<<" Instruction:"<<*I<<"\n";
		    #endif
                    visit.clear();
		    #ifdef WA_BC
		    addRelatedBC(I, argNode, Callee);
		    #endif
                    printRelatedBB(argNode, I, visit, eToS[NORMAL_PTR], argNo);
		    warningSet.insert(argNode);	    
		}
            }
            for (auto obj : nPtsGraph[I][argNode])
            {
                if (obj <= nodeFactory.getConstantIntNode())
                    continue;
                unsigned objSize = nodeFactory.getObjectSize(obj);
                unsigned objOffset = nodeFactory.getObjectOffset(obj);
                for (unsigned i = 0; i < objSize; i++)
                {
		    if (warningReported(I, obj-objOffset+i))
			continue;
		    if (nQualiArray[I].at(obj - objOffset + i) == _UD) {
	                insertUninit(I, obj - objOffset + i, uninitArg);
        	    }

                    if (nQualiArray[I].at(obj - objOffset + i) == _UD)
                    {
			#ifdef PRINTWARN
                        OP<<"***********Warning: argument check fails @ argument "<<argNo<<" : field "<<i<<" not initialized1";
                        OP<<", actual qualifier is "<<nQualiArray[I].at(obj - objOffset + i)<<", nodeIndex = "<<obj - objOffset + i<<"\n";
                        OP<<"[trace] In function @"<<F->getName().str()<<" Instruction:"<<*I<<"\n";
			#endif
                        visit.clear();
			warningTy = eToS[getFieldTy(CI->getArgOperand(argNo)->getType(), i)];
			#ifdef WA_BC
			addRelatedBC(I, argNode, Callee);
			addRelatedBC(I, obj - objOffset + i, Callee);
                        #endif
			printRelatedBB(obj - objOffset + i, I, visit, warningTy, argNo, i);
			warningSet.insert(obj - objOffset + i);
                    }
                }
            }
            continue;
        }
        
        NodeIndex argNode = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
        NodeIndex sumArgNode = Ctx->FSummaries[Callee].args[argNo].getNodeIndex();
        assert(argNode != AndersNodeFactory::InvalidIndex && "Failed to find arg node");

        //else it's the pointer type
	//check weather it's one variable or pointer qualifier
	if (nQualiArray[I].at(argNode) == _UD) {
        	insertUninit(I, argNode, uninitArg);
        }

        if (nQualiArray[I].at(argNode) != _UNKNOWN && nQualiArray[I].at(argNode) < Ctx->FSummaries[Callee].reqVec.at(sumArgNode))
        {   
	    if (!warningReported(I, argNode))
	    {
		#ifdef PRINTWARN
                OP<<"***********Warning: argument check fails @ argument "<<argNo<<" : ptr not initialized, Node "<<argNode<<", actual qualifier = "<<nQualiArray[I].at(argNode)<<"\n";
                OP<<"[trace] In function @"<<F->getName().str()<<" Instruction:"<<*I<<"\n";
		#endif
                visit.clear();
		#ifdef WA_BC
		addRelatedBC(I, argNode, Callee);
                #endif
		printRelatedBB(argNode, I, visit, eToS[NORMAL_PTR], argNo);
		warningSet.insert(argNode);
	    }
        }
	//if the argument is a pointer, then we check the type and the size of the object.
	unsigned checkSize = 0;
	if (CI->getArgOperand(argNo)->getType()->isPointerTy())
	{
		const Type *type = cast<PointerType>(CI->getArgOperand(argNo)->getType())->getElementType();
   		/// An array is considered a single variable of its type.
    		while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
        		type = arrayType->getElementType();
		if (const StructType *structType = dyn_cast<StructType>(type))
		{
			if(structType->isOpaque())
			{
			}
			else if(!structType->isLiteral() && structType->getStructName().startswith("union"))
			{
				checkSize = 1;
			}
			else
			{
				const StructInfo* stInfo = Ctx->structAnalyzer.getStructInfo(structType, M);
				checkSize = stInfo->getExpandedSize();
			}
		}
	}
        for (auto sumObj : Ctx->FSummaries[Callee].sumPtsGraph[sumArgNode])
        {
            unsigned sumObjSize = Ctx->FSummaries[Callee].args[argNo].getObjSize();
            unsigned sumObjOffset = Ctx->FSummaries[Callee].args[argNo].getOffset();
            
            for (auto obj : nPtsGraph[I][argNode])
            {

                if (obj < nodeFactory.getConstantIntNode())
                    continue;
            
                unsigned objSize = nodeFactory.getObjectSize(obj);
                //1. check the obj -> end of the obj
                unsigned objOffset = nodeFactory.getObjectOffset(obj);
                checkSize = std::min(checkSize, sumObjSize);
		checkSize = std::min(checkSize, objSize);
                for (unsigned i = 0; i < checkSize; i++)
                {
                    if (nodeFactory.isUnionObjectNode(obj))
                    {
			if (nQualiArray[I].at(obj) == _ID) {
	                	insertUninit(I, obj, uninitArg);
                        }
                        if (nQualiArray[I].at(obj) == _UD)
                        {
			    if (!warningReported(I, obj))
			    {
				#ifdef PRINTWARN
                                OP<<"***********Warning: argument check fails @ argument "<<argNo<<" some field inside union not initialized2";
                                OP<<", actual qualifier is "<<nQualiArray[I][obj]<<", nodeIndex = "<<obj<<"\n";
                                OP<<"[trace] In function @"<<F->getName().str()<<" Instruction:"<<*I<<"\n";
				#endif
                                visit.clear();
				#ifdef WA_BC
				addRelatedBC(I, argNode, Callee);
				addRelatedBC(I, obj, Callee);
				#endif
                                printRelatedBB(obj, I, visit, "DATA", argNo);
				warningSet.insert(obj);
			    }
                        }
                    }
		    if(obj + i >= nodeFactory.getNumNodes())
			continue;
		    if (nQualiArray[I].at(obj + i) != _ID) {
                        insertUninit(I, obj + i, uninitArg);
                    }

                    if (nQualiArray[I].at(obj + i) != _UNKNOWN && nQualiArray[I].at(obj + i) < Ctx->FSummaries[Callee].reqVec.at(sumObj + i))
                    {
			if (!warningReported(I, obj+i))
			{
			    #ifdef PRINTWARN
                            OP<<"***********Warning: argument check fails @ argument "<<argNo<<" : field "<<i<<" not initialized3";
                            OP<<", actual qualifier is "<<nQualiArray[I].at(obj+i)<<", nodeIndex = "<<obj + i<<"\n";
                            OP<<"[trace] In function @"<<F->getName().str()<<" Instruction:"<<*I<<"\n";
			    #endif
			    warningTy = eToS[getFieldTy(CI->getArgOperand(argNo)->getType(), i)];
                            visit.clear();
			    #ifdef WA_BC
			    addRelatedBC(I, argNode, Callee);
			    addRelatedBC(I, obj+i, Callee);
			    #endif
                            printRelatedBB(obj+i, I, visit, warningTy, argNo, i);
			    warningSet.insert(obj+i);
			}
                    }
                }
                //2. if offset != 0
                if (objOffset > 0 && sumObjOffset > 0)
                {
                    for (unsigned i = 0; i < objOffset; i++)
                    {
			if (nQualiArray[I].at(obj - i) == _UD) {
                            insertUninit(I, obj - i, uninitArg);
                        }

                        if (nQualiArray[I].at(obj-i) != _UNKNOWN && nQualiArray[I].at(obj - i) < Ctx->FSummaries[Callee].reqVec.at(sumObj - i))
                        {
			    if (warningReported(I, obj - i))
				continue;
			    #ifdef PRINTWARN
                            OP<<"***********Warning: argument check fails @ argument "<<argNo<<" : field "<<objOffset - i<<" not initialized";
                            OP<<", actual qualifier is "<<nQualiArray[I].at(obj-i)<<", nodeIndex = "<<obj - i<<"\n";
                            OP<<"[trace] In function @"<<F->getName().str()<<" Instruction:"<<*I<<"\n";
			    #endif
                            visit.clear();
			    warningTy = eToS[getFieldTy(CI->getArgOperand(argNo)->getType(), i)];
			    addRelatedBC(I, argNode, Callee);
			    addRelatedBC(I, obj-i, Callee);
                            printRelatedBB(obj-i, I, visit, warningTy, argNo, objOffset-i);
			    warningSet.insert(obj-i);
                        }
                    }
                }
            }
        }
    }//for arg iterator    
}
void FuncAnalysis::propInitFuncs(llvm::Instruction *I, int* reqArray)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    NodeIndex ptrNode = nodeFactory.getValueNodeFor(CI->getArgOperand(0));
    reqArray[ptrNode] = _ID;
    return;
}
void FuncAnalysis::propCopyFuncs(llvm::Instruction *I, int* reqArray)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    if(CI->getNumArgOperands() < 3)
        return;
    //1. copy the qualifier inference from src to dst
    Value *dst = CI->getArgOperand(0);
    Value *src = CI->getArgOperand(1);
    Value *size = CI->getArgOperand(2);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(dst);
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(src);
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(size);

    reqArray[dstIndex] = _ID;
    reqArray[srcIndex] = _ID;
    reqArray[sizeIndex] = _ID;
    if (!dst->getType()->isPointerTy() || !src->getType()->isPointerTy())
    {
        return;
    }
    for (auto obj : nPtsGraph[I][srcIndex])
    {
        if (obj <= nodeFactory.getConstantIntNode())
            continue;
        unsigned objSize = nodeFactory.getObjectSize(obj);
        unsigned objOffset = nodeFactory.getObjectOffset(obj);
        for (auto dstObj : nPtsGraph[I][dstIndex])
        {
            if (dstObj < nodeFactory.getConstantIntNode())
            {
                for (unsigned i = 0; i < objSize - objOffset; i++)
                {
                    reqArray[dstObj + i] = _ID;
                }
            }
            else{
                for (unsigned i = 0; i < objSize - objOffset; i++)
                {
                    reqArray[dstObj + i] = reqArray[obj + i];
                }
            }
        }
    }
}
void FuncAnalysis::propTransferFuncs(llvm::Instruction *I, int*reqArray)
{
    CallInst *CI = dyn_cast<CallInst>(I);
    //1. copy the qualifier inference from src to dst
    Value *dst = CI->getArgOperand(0);
    Value *src = CI->getArgOperand(1);
    Value *size = CI->getArgOperand(2);
    NodeIndex dstIndex = nodeFactory.getValueNodeFor(dst);
    NodeIndex srcIndex = nodeFactory.getValueNodeFor(src);
    NodeIndex sizeIndex = nodeFactory.getValueNodeFor(size);

    reqArray[dstIndex] = _ID;
    reqArray[srcIndex] = _ID;
    reqArray[sizeIndex] = _ID;

    if (!dst->getType()->isPointerTy() || !src->getType()->isPointerTy())
    {
        return;
    }
    for (auto obj : nPtsGraph[I][srcIndex])
    {
        if (obj <= nodeFactory.getConstantIntNode())
            continue;
        unsigned objSize = nodeFactory.getObjectSize(obj);
        unsigned objOffset = nodeFactory.getObjectOffset(obj);
        for (unsigned i = 0; i < objSize-objOffset; i++)
        {
            reqArray[obj+i] = _ID;
        }
    }
}
void FuncAnalysis::propFuncs(llvm::Instruction *I, llvm::Function *Callee, int* reqArray)
{
    if(Callee == NULL ||Ctx->FSummaries.find(Callee) == Ctx->FSummaries.end())
        return;
    CallInst *CI = dyn_cast<CallInst>(I);
    std::vector<const Argument*> calleeArgs;
    for (auto const &a : Callee->args())
    {   
        const Argument *arg = &a;
        calleeArgs.push_back(arg);
    }
    for (int argNo = 0; argNo < CI->getNumArgOperands(); argNo++)
    {
        NodeIndex argNode = nodeFactory.getValueNodeFor(CI->getArgOperand(argNo));
        NodeIndex sumArgNode = Ctx->FSummaries[Callee].sumNodeFactory.getValueNodeFor(calleeArgs.at(argNo));
        NodeIndex sumArgObjNode = 0;
        for (auto sumObj : Ctx->FSummaries[Callee].sumPtsGraph[sumArgNode])
        {
            sumArgObjNode = sumObj;
        }
        unsigned sumArgObjOffset = Ctx->FSummaries[Callee].sumNodeFactory.getObjectOffset(sumArgObjNode);
        unsigned sumArgObjSize = Ctx->FSummaries[Callee].sumNodeFactory.getObjectSize(sumArgObjNode);
        for (auto argObj : nPtsGraph[I][argNode])
        {
            unsigned objOffset = nodeFactory.getObjectOffset(argObj);
            unsigned objSize = nodeFactory.getObjectSize(argObj);
            for(unsigned i = sumArgObjOffset; i < sumArgObjSize; i++)
            {
                if(Ctx->FSummaries[Callee].reqVec.at(sumArgObjNode + i) == _ID)
                    reqArray[argObj + i] = _ID;
            }
            if (objOffset != 0)
            {
                for (unsigned i = 0; i < sumArgObjOffset; i++)
                {
                    if(Ctx->FSummaries[Callee].reqVec.at(sumArgObjNode - i) == _ID)
                        reqArray[argObj - i] = _ID;
                }
            }
        }
    }
}
#ifdef dbg
void printAllocationBB(llvm::Instruction *I)
{
    switch(I->getOpcode())
    {
        case Instruction::Load:
        {
            //Find the allocation sight
            if(llvm::AllocaInst *AI = dyn_cast<AllocaInst*>(I->getOperand(0)))
            {
                OP<<"---related BB: "<<*AI<<"\n";
                return;
            }
            else{
                printAllocationBB(I->getOperand(0));
            }
            
        }
    }
}
#endif
