//===- FlowSensitiveStruct.cpp -- flow-sensitive type filter ------------//

/*
 * FlowSensitiveStruct.cpp
 *
 *  Created on: Oct 08, 2019
 *      Author: Mohamad Barbar
 */




#include "Util/Options.h"
#include "SVF-FE/DCHG.h"
#include "Util/SVFModule.h"
#include "WPA/WPAStat.h"
#include "WPA/FlowSensitive.h"
#include "WPA/FlowSensitiveStruct.h"
#include "WPA/Andersen.h"
#include "MemoryModel/PointsTo.h"
#include "llvm/Demangle/Demangle.h"


using namespace SVF;

/// Whether we allow reuse for TBHC.

//这里可能还需要添加别的类进行继承
// FlowSensitiveStruct::FlowSensitiveStruct(SVFIR* _pag, PTATY type = FSSPARSE_WPA) : FlowSensitive(_pag, type)
// {
//     // Using `this` as the argument for TypeBasedHeapCloning is okay. As PointerAnalysis, it's
//     // already constructed. TypeBasedHeapCloning also doesn't use pta in the constructor so it
//     // just needs to be allocated, which it is.

// }

void FlowSensitiveStruct::analyze()
{
    bool limitTimerSet = SVFUtil::startAnalysisLimitTimer(Options::FsTimeLimit);

    /// Initialization for the Solver

    initialize();


    double start = stat->getClk(true);
    /// Start solving constraints
    //DBOUT(DGENERAL, outs() << SVFUtil::pasMsg("Start Solving Constraints\n"));

    do
    {
        numOfIteration++;

        if(0 == numOfIteration % OnTheFlyIterBudgetForStat)
            dumpStat();

        callGraphSCC->find();

        initWorklist();
        solveWorklist();
        //SVFUtil::outs() << "analyze"  << "\n";
    }
    while (updateCallGraph(getIndirectCallsites()));

    //DBOUT(DGENERAL, outs() << SVFUtil::pasMsg("Finish Solving Constraints\n"));


    // Reset the time-up alarm; analysis is done.
    SVFUtil::stopAnalysisLimitTimer(limitTimerSet);

    double end = stat->getClk(true);
    solveTime += (end - start) / TIMEINTERVAL;

    
    /// finalize the analysis
    std::cout<< "processTime:"<< processTime <<"\n";
    
    //  std::cout<< "more than one type" << "\n";
    // std::cout<< "bitCastinstuct:"<< castInstSet.size() <<"\n";
    // std::cout<< "bitCastinstuctWork:"<< bitCastinstuctWork <<"\n";
    int structNum = 0;
    int structnotFlatMost = 0;
    for(auto& typeKey : allStruct2FldOff){
        if(typeKey.first->isStructTy()){
            structNum++;
            llvm::StructType* structType = llvm::dyn_cast<llvm::StructType>(typeKey.first);
            int numElements = structType->getNumElements();
            if(numElements > structnotFlatMost){
                structnotFlatMost = numElements;
            }
        }else if(typeKey.first->isArrayTy()){
            structNum++;
            int numElements = typeKey.first->getArrayNumElements();
            if(numElements > structnotFlatMost){
                structnotFlatMost = numElements;
            }
        }else if(typeKey.first->isVectorTy()){
            structNum++;
            if(llvm::FixedVectorType* vecTypeFix = llvm::dyn_cast<llvm::FixedVectorType>(typeKey.first)){
                int numElements = vecTypeFix->getNumElements();
                if(numElements > structnotFlatMost){
                    structnotFlatMost = numElements;
                }
               
            }
        }
    }
    
    std::cout<< "structNum:"<< structNum <<"\n";
    // int structnotFlatMost = 0;
    // for(auto& typeKey: allStruct2Fld){
    //     int tmpCount = 0;
    //     for(auto& subTypeKey : typeKey.second){
    //         if(subTypeKey.first->isStructTy()){
    //             tmpCount++;
    //         }else if(subTypeKey.first->isArrayTy()){
    //             tmpCount++;
    //         }else if(subTypeKey.first->isVectorTy()){
    //             tmpCount++;
    //         }
    //     }
    //     if(tmpCount > structnotFlatMost){
    //         structnotFlatMost = tmpCount;
    //     }
    // }
    std::cout<< "structnotFlatMost:"<< structnotFlatMost <<"\n";
    unsigned structFlatMost = 0;
    //Type* mostTypett = nullptr;
    for(auto& typeKey :  allStruct2FldOff){
        if(typeKey.second.size() > structFlatMost){
            structFlatMost = typeKey.second.size();
            //mostTypett = typeKey.first;
        }
    }
    std::cout<< "structFlatMost:"<< structFlatMost <<"\n";

    // std::string str0;
    //     llvm::raw_string_ostream rso0(str0);
    //     mostTypett->print(rso0);
    //     rso0.flush();
    //     std::cout << "type:"<< str0 << "\n";
    // std::cout<< "objNum1:"<< getPAG()->getObjectNodeNum() <<"\n";
    //  std::cout<< "objNum2:"<< getPAG()->getTotalNodeNum()  <<"\n";
    // std::cout<< "subobjNum:"<< getPAG()->getFieldObjNodeNum() <<"\n";
    
    int allObjType = 0;
    map<NodeID,int> objMoreThanOneType;
    for(const auto & objKey : typeSet){
        //int tmpCount = 0;
        
        for(const auto &idxKey : objKey.second){
            int tmpType = 0;
            //int tmpSubType = 0;
            map<int,int> tmpSubType;
            for(const auto& typeKey : idxKey.second){
                if(typeKey.second == 0){
                    tmpType++ ;
                    allObjType++;
                }
            }
            if(typeMap[objKey.first].find(idxKey.first) == typeMap[objKey.first].end()){
                typeMap[objKey.first][idxKey.first] = tmpType;
            }else{
                typeMap[objKey.first][idxKey.first] = typeMap[objKey.first][idxKey.first] + tmpType;
            }
            if(tmpType > 1){
                if(objMoreThanOneType.find(objKey.first) == objMoreThanOneType.end()){
                    objMoreThanOneType[objKey.first] = 3;
                }else{
                    objMoreThanOneType[objKey.first] = 3;
                }  
            }
             
            
        }

    }
    // // std::cout<< "objMostType:"<< objWithMostType <<"\n";
    // // std::cout<< "objAveType:"<< objWithMostType <<"\n";
    int moreThanOneCount = 0;
    for(auto & objKey : objMoreThanOneType){
        if(objKey.second > 1){
            moreThanOneCount++;
        }
    }
    std::cout<< "moreThanOneCount:" << moreThanOneCount << "\n";

    int mostType = 0;
    
    for(auto & objKey : typeMap){
        for(auto& typeNumKey : objKey.second){
            if(typeNumKey.second > 1){
                //std::cout<< "obj:" << objKey.first << "  typeIdx:" << typeNumKey.first << "  thisCount:"<< typeNumKey.second <<"\n";
                if(mostType < typeNumKey.second){
                    mostType = typeNumKey.second;
                }
                
            }
            
        }
    }
    std::cout<< "mostType:" << mostType << "\n";

    //std::cout<< "allObjType:" << allObjType << "\n";

    // int subObjTypeMost = 0;
    // for(auto & objKey : typeSubMap){
    //     for(auto& typeNumKey : objKey.second){
    //         for(auto& offKey : typeNumKey.second){
    //             if(offKey.second > subObjTypeMost){
    //                 subObjTypeMost = offKey.second ;
    //             }
    //             // if(offKey.second > 1)
    //             //     std::cout<< "obj:" << objKey.first << "  typeIdx:" << typeNumKey.first  << "  offset:"<< offKey.first <<"  thisCount:"<< offKey.second <<"\n";
    //         }
            
    //     }
    // }
    // std::cout<< "subObjTypeMost:" << subObjTypeMost << "\n";

    //std::cout<< "allObjSize:" << allObj.count() << "\n";

    int objCount = 0;
    for(NodeID o :  allObj){
        NodeID baseId = getBaseObjVar(o);
        if(baseId == o){
            objCount++;
        }
    }
    std::cout<< "baseObjNum:" << objCount << "\n";
    std::cout<< "---------------------------------"  << "\n";
    //stat->performStat();
    printCTirAliasStats();
    finalize();

}

void FlowSensitiveStruct::initialize()
{

    // for (u32_t i = 0; i < LLVMModuleSet::getLLVMModuleSet()->getModuleNum(); ++i)
    // {
    //     Module *M = LLVMModuleSet::getLLVMModuleSet()->getModule(i);
    //      for (StructType *ST : M->getIdentifiedStructTypes()) {
    //         // We found a struct type
    //         // llvm::errs() << "Struct:------ " << ST->getName() << "\n";
    //         // ST->print(llvm::errs());
    //         // SVFUtil::outs()  <<  "\n";
    //         //按模块分类。
    //         // string className = cppUtil::getClassNameFromType(ST);
    //         // SVFUtil::outs()  << "Struct: " << className << "\n";
            

    //     }


    // }

    PointerAnalysis::initialize();

    stat = new FlowSensitiveStat(this);

    // TODO: support clustered aux. Andersen's.
    assert(!Options::ClusterAnder && "FlowSensitive::initialize: clustering auxiliary Andersen's unsupported.");
    ander = AndersenWaveDiff::createAndersenWaveDiff(getPAG());

    // If cluster option is not set, it will give us a no-mapping points-to set.
    assert(!(Options::ClusterFs && Options::PlainMappingFs)
           && "FS::init: plain-mapping and cluster-fs are mutually exclusive.");
    if (Options::ClusterFs)
    {
        cluster();
        // Reset the points-to cache although empty so the new mapping could
        // be applied to the inserted empty set.
        getPtCache().reset();
    }
    else if (Options::PlainMappingFs)
    {
        plainMap();
        // As above.
        getPtCache().reset();
    }

    svfg = memSSA.buildFullSVFG(ander);

    setGraph(svfg);


}

void FlowSensitiveStruct::finalize(void)
{
    // std::cout<< " loadCheck:"<<loadCheck << "\n";
    // std::cout<< " retCheck:"<<retCheck << "\n";
    // std::cout<< " paramCheck:"<<paramCheck << "\n";
    // std::cout<< " storeCheck:"<<storeCheck << "\n";
    // std::cout<< " addCheck:"<<addCheck << "\n";
   


    FlowSensitive::finalize();
    // ^ Will print call graph and alias stats.


}





bool FlowSensitiveStruct::propAlongDirectEdge(const DirectSVFGEdge* edge)
{

    bool changed = FlowSensitive::propAlongDirectEdge(edge);
    return changed;
}

/*!
 * Propagate points-to information from actual-param to formal-param.
 *  Not necessary if SVFGOPT is used instead of original SVFG.
 */



bool FlowSensitiveStruct::propagateFromAPToFP(const ActualParmSVFGNode* ap, const SVFGNode* dst)
{
    
    const FormalParmSVFGNode* fp = SVFUtil::dyn_cast<FormalParmSVFGNode>(dst);
    assert(fp && "expecting a formal param node");
    
    NodeID pagDst = fp->getParam()->getId();
    NodeID srcId = ap->getParam()->getId();
    const PointsTo &srcCPts = getPts(srcId);


    //we need to get ctor set.
    bool ctorFlag = false;

    const SVFFunction* CtorSVF = fp->getFun();
    if(CtorSVF->arg_size() > 0){
        const Function* CtorFun = CtorSVF->getLLVMFun();
        
        const PAGNode* cParaPAG = fp->getParam();
        const Value* cPara = cParaPAG->getValue();
    
        if(ctorSet.find(CtorFun) != ctorSet.end()){
            const Value* firstPara = CtorSVF->getArg(0);

            if(firstPara == cPara && cParaPAG->isPointer()){
                
                llvm::Type *paraType = cPara->getType()->isPointerTy() ? cPara->getType()->getPointerElementType() : cPara->getType();

                // std::string str0;
                // llvm::raw_string_ostream rso0(str0);
                // paraType->print(rso0);
                // rso0.flush();
                // std::cout << "initType:"<< str0 << "\n";

                for(auto o: srcCPts ){

                    //std::cout << "object:"<< getPAG()->getGNode(o)->toString()   <<"\n";

                    copyTypePAGUniq(o, srcId,pagDst);
                    auto iterSubFld = struct2subFld.find(paraType);  //here use struct2subFld will be ok ? 
                    if(iterSubFld != struct2subFld.end()){
                        for(const auto& subType :iterSubFld->second){
                            ptrVir[o][paraType].insert(subType.first);

                            // std::string str1;
                            // llvm::raw_string_ostream rso1(str1);
                            // subType.first->print(rso1);
                            // rso1.flush();
                            // std::cout << "subType:"<< str1 << "\n";

                        }
                    }
                    ptrVir[o][paraType].insert(paraType);


                }

                ctorFlag = true;
            }
            else{
                std::cout << "ctor first not pointer" <<std::endl;
            }
        }
    }else{
        //we should not pass anything
        //but i tend to think that before part make sure of that.
    }
    
    if(!ctorFlag){
        for(auto o: srcCPts ){ 
            copyTypePAGUniq(o, srcId,pagDst);
        }
    }


    //changed = unionPts(pagDst, srcCPts);
    bool changed = unionPts(pagDst, srcCPts);

    return changed;




}

/*!
 * Propagate points-to information from formal-ret to actual-ret.
 * Not necessary if SVFGOPT is used instead of original SVFG.
 */
bool FlowSensitiveStruct::propagateFromFRToAR(const FormalRetSVFGNode* fr, const SVFGNode* dst)
{


    const ActualRetSVFGNode* ar = SVFUtil::dyn_cast<ActualRetSVFGNode>(dst);
    assert(ar && "expecting an actual return node");
    NodeID pagDst = ar->getRev()->getId();
    NodeID srcId = fr->getRet()->getId();
    const PointsTo & srcCPts = getPts(srcId);

    
    bool changed = unionPts(pagDst, srcCPts);
    for(auto o: srcCPts){
        copyTypePAGUniq(o, srcId,pagDst);
    }

    return changed;
}

bool FlowSensitiveStruct::propAlongIndirectEdge(const IndirectSVFGEdge* edge)  //here nothing change compared to FlowSensitive, it is the same
{
    //SVFUtil::outs() << "propAlongIndirectEdge--:"<<edge->toString()   <<"\n";
    double start = stat->getClk();

    SVFGNode* src = edge->getSrcNode();
    SVFGNode* dst = edge->getDstNode();

    // SVFUtil::outs() << "propAlongIndirectEdge--src:"<< src->toString()   <<"\n";
    // SVFUtil::outs() << "propAlongIndirectEdge***dst:"<< dst->toString()   <<"\n";
    bool changed = false;

    // Get points-to targets may be used by next SVFG node.
    // Propagate points-to set for node used in dst.
    const NodeBS& pts = edge->getPointsTo();
    for (NodeBS::iterator ptdIt = pts.begin(), ptdEit = pts.end(); ptdIt != ptdEit; ++ptdIt)
    {
        NodeID ptd = *ptdIt;

        if (propVarPtsFromSrcToDst(ptd, src, dst))
            changed = true;

        if (isFieldInsensitive(ptd))
        {
            /// If this is a field-insensitive obj, propagate all field node's pts
            const NodeBS& allFields = getAllFieldsObjVars(ptd);
            for (NodeBS::iterator fieldIt = allFields.begin(), fieldEit = allFields.end();
                    fieldIt != fieldEit; ++fieldIt)
            {
                if (propVarPtsFromSrcToDst(*fieldIt, src, dst))
                    changed = true;
            }
        }


    }

    double end = stat->getClk();
    indirectPropaTime += (end - start) / TIMEINTERVAL;


    return changed;


}




/*!
 * Propagate points-to information of a certain variable from src to dst.
 */
bool FlowSensitiveStruct::propVarPtsFromSrcToDst(NodeID var, const SVFGNode* src, const SVFGNode* dst)
{
    bool changed = false;
    if (SVFUtil::isa<StoreSVFGNode>(src))
    {
        //need to copy pair() type set to current?
        //here are svfg type copy
        if (updateInFromOut(src, var, dst, var)){
            changed = true;
            //get object is enough
            //
            const PointsTo& tmpOutPts = getDFOutPtsSet(src,var);
            for(auto o : tmpOutPts){
                //copy 
                copyTypeSVFGUniq(o, src->getId(), var, dst->getId(), var);
            }


        }
            
        if(changed){
            //SVFUtil::outs() << "firstType--:"<< var << " "  <<"\n";
        }
        
    }
    else
    {
        if (updateInFromIn(src, var, dst, var)){
            changed = true;
            const PointsTo& tmpOutPts = getDFInPtsSet(src,var);
            for(auto o : tmpOutPts){
                //copy 
                copyTypeSVFGUniq(o, src->getId(), var, dst->getId(), var);
            }
        }
            
        if(changed){
            //SVFUtil::outs() << "secondType--:" << var << " " <<"\n";
        }
        
    }
    return changed;
}






bool FlowSensitiveStruct::processAddr(const AddrSVFGNode* addr)
{

    
    double start = stat->getClk();
    NodeID srcID = addr->getPAGSrcNodeID();
    NodeID dstID = addr->getPAGDstNodeID();
    if (isFieldInsensitive(srcID)){
        //SVFUtil::outs() << "isFieldInsensitive:"   <<"\n";
        srcID = getFIObjVar(srcID);
    }

    
    bool changed = addPts(dstID, srcID);
    //at this kind of node,we do not need to copy object type.

    //for struct, we need to consider global value.
    //like this:processAddr:AddrVFGNode ID: 34 AddrStmt: [Var93 <-- Var96]
//  @_ZTV5Right = linkonce_odr dso_local unnamed_addr constant { [4 x i8*], [4 x i8*] } { [4 x i8*] [i8* null, i8* bitcast ({ i8*, i8*, i32, i32, i8*, i64, i8*, i64 }* @_ZTI5Right to i8*), i8* bitcast (i8* (%struct.Right*)* @_ZN5Right6behaveEv to i8*), i8* bitcast (void (%struct.Base1*)* @_ZN5Base17baseVirEv to i8*)], [4 x i8*] [i8* inttoptr (i64 -8 to i8*), i8* bitcast ({ i8*, i8*, i32, i32, i8*, i64, i8*, i64 }* @_ZTI5Right to i8*), i8* bitcast (i8* (%struct.Right*)* @_ZThn8_N5Right6behaveEv to i8*), i8* bitcast (void (%struct.Base2*)* @_ZN5Base27baseVirEv to i8*)] }, comdat, align 8 { Glob  }
// ******:{ [4 x i8*], [4 x i8*] }
//analysis

    Type* typeToCheck = addr->getValue() ? addr->getValue()->getType() : nullptr;
    if(typeToCheck) {
        llvm::Type *resolvedType = typeToCheck->isPointerTy() ? typeToCheck->getPointerElementType() : typeToCheck;

        
        //we should only add struct
        if(resolvedType->isStructTy()){
            addType2ptrNodeUniq(srcID, srcID, dstID, resolvedType);
        }else if(resolvedType->isArrayTy()){
            addType2ptrNodeUniq(srcID, srcID, dstID, resolvedType);
        }else if(resolvedType->isVectorTy()){
            addType2ptrNodeUniq(srcID, srcID, dstID, resolvedType);
        }


    }else{
        SVFUtil::outs() << "processAddr type is null ptr:"<< addr->toString()   <<"\n";
    }

    if (isHeapMemObj(srcID))
    {
        heapObjFlag.insert(srcID);
    }
    //for heap object,we need to get it's size 
    //and we need to get the times of struct for this kind of edge


    double end = stat->getClk();
    addrTime += (end - start) / TIMEINTERVAL;

    const PointsTo& tmpAddPts = getPts(addr->getPAGDstNodeID());
    allObj |= tmpAddPts; 

    return changed; 
}


bool FlowSensitiveStruct::processGep(const GepSVFGNode* edge)
{
    double start = stat->getClk();
    
    NodeID srcID = edge->getPAGSrcNodeID();
    NodeID dstID = edge->getPAGDstNodeID();
    
    bool changed = false;
    // Helper function to get the element type if the given type is a pointer.
    auto getElementType = [](Type* t) -> Type* {
        return t->isPointerTy() ? t->getPointerElementType() : t;
    };
    const PointsTo& srcPts = getPts(srcID);
    const llvm::GetElementPtrInst* gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(edge->getPAGDstNode()->getValue());
    if (!gepInst) { // just copy type and add type in this branch

        const GepStmt* gepStmt = SVFUtil::cast<GepStmt>(edge->getPAGEdge());
        const llvm::Value * gepVal = gepStmt->getValue();
        if(gepVal != nullptr){
            Type* dstType = gepVal->getType()->isPointerTy() ? gepVal->getType()->getPointerElementType() : gepVal->getType();
            PointsTo tmpDstPts;
            const GepStmt* gepStmt = SVFUtil::cast<GepStmt>(edge->getPAGEdge());
            if (gepStmt->isVariantFieldGep())
            {
                for (NodeID o : srcPts)
                {
                    
                    if (isBlkObjOrConstantObj(o))
                    {
                        tmpDstPts.set(o);
                        copyTypePAGUniq(o, srcID,dstID);
                        continue;
                    }

                    setObjFieldInsensitive(o);
                    NodeID fi_o = getFIObjVar(o);
                    tmpDstPts.set(fi_o);
                    // if(dstType->isStructTy()){
                    //     addType2ptrNodeUniq(fi_o, srcID, dstID, dstType);
                    // }else if(dstType->isArrayTy()){
                    //     addType2ptrNodeUniq(fi_o, srcID, dstID, dstType);
                    // }else if(dstType->isVectorTy()){
                    //     addType2ptrNodeUniq(fi_o, srcID, dstID, dstType);
                    // }else{
                        copyTypePAGUniq(fi_o, srcID,dstID);
                    //}
                    //addType2ptrNodeUniq(o, srcID, dstID, dstType);
                }
            }
            else
            {
                for (NodeID o : srcPts)
                {
                    
                    if (isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
                    {
                        tmpDstPts.set(o);
                        copyTypePAGUniq(o, srcID,dstID);
                        continue;
                    }

                    NodeID fieldSrcPtdNode = getGepObjVar(o, gepStmt->getLocationSet());
                    tmpDstPts.set(fieldSrcPtdNode);
                    if(dstType->isStructTy()){
                        addType2ptrNodeUniq(fieldSrcPtdNode, srcID, dstID, dstType);
                    }else if(dstType->isArrayTy()){
                        addType2ptrNodeUniq(fieldSrcPtdNode, srcID, dstID, dstType);
                    }else if(dstType->isVectorTy()){
                        addType2ptrNodeUniq(fieldSrcPtdNode, srcID, dstID, dstType);
                    }else{
                        copyTypePAGUniq(fieldSrcPtdNode, srcID,dstID);
                    }
                    
                }
            }
            //SVFUtil::outs() << "processGep 123dstValue is null:" << edge->toString() << "\n";
            if (unionPts(dstID, tmpDstPts))
                changed = true;
        }else{ //just copy object and copy type
            PointsTo tmpDstPts;
            const GepStmt* gepStmt = SVFUtil::cast<GepStmt>(edge->getPAGEdge());
            //SVFUtil::outs() << "processGep dstValue 22is null:" << edge->toString() << "\n";
            if (gepStmt->isVariantFieldGep())
            {
                for (NodeID o : srcPts)
                {
                    //copyTypePAGUniq(o, srcID,dstID);
                    if (isBlkObjOrConstantObj(o))
                    {
                        tmpDstPts.set(o);
                        continue;
                    }

                    setObjFieldInsensitive(o);
                    NodeID fi_o = getFIObjVar(o);
                    copyTypePAGUniq(fi_o, srcID,dstID);
                    tmpDstPts.set(fi_o);
                }
            }
            else
            {
                for (NodeID o : srcPts)
                {
                    
                    if (isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
                    {
                        tmpDstPts.set(o);
                        continue;
                    }

                    NodeID fieldSrcPtdNode = getGepObjVar(o, gepStmt->getLocationSet());
                    copyTypePAGUniq(fieldSrcPtdNode, srcID,dstID);
                    tmpDstPts.set(fieldSrcPtdNode);
                }
            }
            //SVFUtil::outs() << "processGep22 dstValue is null:" << edge->toString() << "\n";
            if (unionPts(dstID, tmpDstPts))
                changed = true;
        }
    }else{
        Type* gepDstType = getElementType(gepInst->getType());
        //Type* gepSrcType = getElementType(gepInst->getPointerOperandType());


        //SVFUtil::outs() << "processGep dstValue 33is null:" << edge->toString() << "\n";

        PointsTo tmpDstPts;
        const GepStmt* gepStmt = SVFUtil::cast<GepStmt>(edge->getPAGEdge());


        if (gepStmt->isVariantFieldGep()){
            for (NodeID o : srcPts)
            {
                if (isBlkObjOrConstantObj(o))  //here need more consider 
                {
                    tmpDstPts.set(o);
                    copyTypePAGUniq(o, srcID, dstID);
                    continue;
                }

                setObjFieldInsensitive(o);
                NodeID fi_o = getFIObjVar(o);
                tmpDstPts.set(fi_o);
                // if(gepDstType->isStructTy()){
                //     addType2ptrNodeUniq(fi_o, srcID, dstID, gepDstType);
                // }else if(gepDstType->isArrayTy()){
                //     addType2ptrNodeUniq(fi_o, srcID, dstID, gepDstType);
                // }else if(gepDstType->isVectorTy()){
                //     addType2ptrNodeUniq(fi_o, srcID, dstID, gepDstType);
                // }else{
                    copyTypePAGUniq(fi_o, srcID,dstID);
                //}
                
                // NodeID baseid = getBaseObjVar(fi_o);
                // SVFUtil::outs() << "fi_o2:"<< fi_o << "baseid2:"<< baseid  <<"\n";
                // tmpDstPts.set(fi_o);

            }
        }else{
            for (NodeID o : srcPts)
            {
                if (isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
                {
                    tmpDstPts.set(o);  //just 
                    copyTypePAGUniq(o, srcID, dstID);
                    continue;
                }
                //here should check the type first
                // then create new object, if can not find type do nothing.
                s32_t realOffset = gepStmt->getLocationSet().getFldOff();
                if(checkGepInst(o, srcID, realOffset)){
                    
                    NodeID fieldSrcPtdNode = getGepObjVar(o, gepStmt->getLocationSet());
                    tmpDstPts.set(fieldSrcPtdNode);
                    if(gepDstType->isStructTy()){
                        addType2ptrNodeUniq(fieldSrcPtdNode, srcID, dstID, gepDstType);
                    }else if(gepDstType->isArrayTy()){
                        addType2ptrNodeUniq(fieldSrcPtdNode, srcID, dstID, gepDstType);
                    }else if(gepDstType->isVectorTy()){
                        addType2ptrNodeUniq(fieldSrcPtdNode, srcID, dstID, gepDstType);
                    }else{
                        copyTypePAGUniq(fieldSrcPtdNode, srcID,dstID);
                    }
                
                }else{
                    // SVFUtil::outs() << "---------------------------------------\n";
                    // SVFUtil::outs() << "processGeper222:" << edge->toString() << "\n";
                    // SVFUtil::outs() << "processGeperReal~:" << realOffset << "\n";
                    // std::cout << "points-to----:"<< getPAG()->getGNode(o)->toString()   <<"\n";
                    
                }

                
            }
        }

        //SVFUtil::outs() << "processGep dstValue 34is null:" << edge->toString() << "\n";
        changed = unionPts(dstID, tmpDstPts);
        //SVFUtil::outs() << "processGep -dstValue 34is null:" << edge->toString() << "\n";
    }

 
    //SVFUtil::outs() << "processGep dstValue 35is null:" << edge->toString() << "\n";
    double end = stat->getClk();
    gepTime += (end - start) / TIMEINTERVAL;
    const PointsTo& tmpAddPts = getPts(dstID);
    allObj |= tmpAddPts; 
    //SVFUtil::outs() << "processGep dstValue 36is null:" << edge->toString() << "\n";
    return changed;






}




bool FlowSensitiveStruct::processLoad(const LoadSVFGNode* load)
{

    //SVFUtil::outs() << "load))):"<< load->toString()   <<"\n";
    // SVFUtil::outs() <<"loadsrc:" <<getPAG()->getGNode(load->getPAGSrcNodeID())->toString() 
    // << "--dst:"<< getPAG()->getGNode(load->getPAGDstNodeID())->toString()  <<"\n";
    
    double start = stat->getClk();
    bool changed = false;


    NodeID loadID = load->getId();
    NodeID dstVar = load->getPAGDstNodeID();
    NodeID srcID = load->getPAGSrcNodeID();



    const PointsTo& srcPts = getPts(srcID);

   
    for (PointsTo::iterator ptdIt = srcPts.begin(); ptdIt != srcPts.end(); ++ptdIt)
    {
        NodeID ptd = *ptdIt;

        if (pag->isConstantObj(ptd) || pag->isNonPointerObj(ptd))
            continue;

        if (unionPtsFromIn(load, ptd, dstVar)){
            changed = true;
            //do not anything
            //just copy the type to current loc
            //but we need to get the pts
            const PointsTo& tmpPts = getDFInPtsSet(load, ptd);
            for(auto o: tmpPts){
                //copyTypePAG2SVFG(o, NodeID srcID, NodeID loc, NodeID ptd);
                //copyTypeSVFG2PAG
                copyTypeSVFG2PAGUniq(o, dstVar, loadID, ptd);
            }

        }
            
        

        if (isFieldInsensitive(ptd))
        {
            /// If the ptd is a field-insensitive node, we should also get all field nodes'
            /// points-to sets and pass them to pagDst.
            const NodeBS& allFields = getAllFieldsObjVars(ptd);
            for (NodeBS::iterator fieldIt = allFields.begin(), fieldEit = allFields.end();
                    fieldIt != fieldEit; ++fieldIt)
            {
                if (unionPtsFromIn(load, *fieldIt, dstVar)){
                    changed = true;
                    //do not anything
                    //just copy the type to current loc
                    const PointsTo& tmpPtsFld = getDFInPtsSet(load, *fieldIt);
                    for(auto o: tmpPtsFld){

                        copyTypeSVFG2PAGUniq(o, dstVar, loadID, ptd);
                    }
                }
                    
            }
        }
    }
    
    //SVFUtil::outs() << "load) end)):"<< load->toString()   <<"\n";
    //SVFUtil::outs() << "loadchanged:"<< changed   <<"\n";
    double end = stat->getClk();
    loadTime += (end - start) / TIMEINTERVAL;
    const PointsTo& tmpAddPts = getPts(dstVar);
    allObj |= tmpAddPts; 
    return changed;
}






bool FlowSensitiveStruct::processStore(const StoreSVFGNode* store)
{

    
    // SVFUtil::outs() <<"storeSrc:" <<getPAG()->getGNode(store->getPAGSrcNodeID())->toString() 
    // << "--storeDst:"<< getPAG()->getGNode(store->getPAGDstNodeID())->toString()  <<"\n";


    NodeID storeID = store->getId();
    NodeID srcID = store->getPAGSrcNodeID();
    NodeID dstID = store->getPAGDstNodeID();
    //const Instruction* inst =  store->getInst();

    const PointsTo & dstPts = getPts(dstID);

    if (dstPts.empty())
        return false;

    double start = stat->getClk();
    bool changed = false;



    if(getPts(srcID).empty() == false)
    {
        const PointsTo & srcPts = getPts(srcID);

        for (PointsTo::iterator it = dstPts.begin(), eit = dstPts.end(); it != eit; ++it)
        {
            NodeID ptd = *it;

            if (pag->isConstantObj(ptd) || pag->isNonPointerObj(ptd))
                continue;

            //SVFUtil::outs() << "ptd:"<< ptd   <<"\n";
            //SVFUtil::outs() <<"ptdNode:" <<getPAG()->getGNode(ptd)->toString();

            if (unionPtsFromTop(store, srcID, ptd)){
                changed = true;
                //just need to copy the type src object include to current loc.
                // but this time the loc is pair set
                for(auto o: srcPts){
                    //copy type to current loc
                    copyTypePAG2SVFGUniq(o, srcID, storeID, ptd);
                }
            }
                
        }

      

        
    }


    double end = stat->getClk();
    storeTime += (end - start) / TIMEINTERVAL;

    double updateStart = stat->getClk();
    // also merge the DFInSet to DFOutSet.
    /// check if this is a strong updates store
    NodeID singleton;
    bool isSU = isStrongUpdate(store, singleton);
    if (isSU)
    {
        svfgHasSU.set(store->getId());
        if (strongUpdateOutFromIn(store, singleton))
            changed = true;
    }
    else
    {
        svfgHasSU.reset(store->getId());
        if (weakUpdateOutFromIn(store))
            changed = true;
    }
    double updateEnd = stat->getClk();
    updateTime += (updateEnd - updateStart) / TIMEINTERVAL;

    // const PointsTo& tmpAddPts = getPts(dstVar);
    // allObj |= tmpAddPts; 

    return changed;
}

bool FlowSensitiveStruct::processPhi(const PHISVFGNode* phi)
{
    //SVFUtil::outs() << "processPhi))):"<< phi->toString()   <<"\n";
    double start = stat->getClk();
    bool changed = false;
    NodeID pagDst = phi->getRes()->getId();
    for (PHISVFGNode::OPVers::const_iterator it = phi->opVerBegin(), eit = phi->opVerEnd();	it != eit; ++it)
    {
        NodeID src = it->second->getId();
        const PointsTo& srcPts = getPts(src);
        //SVFUtil::outs() << "aaa5"   <<"\n";
        if (unionPts(pagDst, srcPts)){
            changed = true;
            //copy need to consider about object different type set merge
            //the phi node can not use type to filter out object.
            for(auto o : srcPts){
                copyTypePAGUniq(o,src,pagDst);
            }
        }
            
    }
    //SVFUtil::outs() << "processPhi))end):"<< phi->toString()   <<"\n";
    double end = stat->getClk();
    phiTime += (end - start) / TIMEINTERVAL;
    const PointsTo& tmpAddPts = getPts(pagDst);
    allObj |= tmpAddPts; 
    return changed;
}

/// Returns whether this instruction initialisates an object's
/// vtable (metadata: ctir.vt.init). Returns the object's type,
/// otherwise, nullptr.

bool FlowSensitiveStruct::processCopy(const CopySVFGNode* copy)
{

    double start = stat->getClk();


    NodeID srcID = copy->getPAGSrcNodeID();
    NodeID dstID = copy->getPAGDstNodeID();
    //dynamic_cast the srcId should only the first argument,so here we use the srcID will be ok.
    //can not just union those pts , due to dynamic_cast are also copy
    bool changed = false;
    


    const PointsTo& srcPts = getPts(srcID);
    

    const Instruction* inst =  copy->getInst();

    

    if(inst != nullptr){

        if(llvm::isa<CastInst>(inst)){
            const CastInst* castInst = llvm::dyn_cast<CastInst>(inst);
            //castInstSet.emplace(inst);
            //bitCastinstuct++;
            llvm::Type *destType = castInst->getDestTy()->isPointerTy() ? castInst->getDestTy()->getPointerElementType() : castInst->getDestTy() ;


            //llvm::Type *srcType = castInst->getSrcTy()->isPointerTy() ? castInst->getSrcTy()->getPointerElementType() : castInst->getSrcTy();

            for(NodeID o : srcPts){  //here error

                //we should only add struct type
                //and we should not filter out type
                //we just do add type not use filter out type
                //std::cout << "bitcast-:"<< o << std::endl;
                //bitCastinstuctWork++;
                bitCastObj = bitCastObj + 1;
                if(destType->isStructTy()){
                    //we have to check if add copy object
                    addType2ptrNodeUniq(o, srcID, dstID, destType);   
                }else if(destType->isArrayTy()){
                    addType2ptrNodeUniq(o, srcID, dstID, destType); 
                }else if(destType->isVectorTy()){
                    addType2ptrNodeUniq(o, srcID, dstID, destType); 
                }
                else{
                    copyTypePAGUniq(o, srcID, dstID);
                }

                //tmpDstPts.set(o);
            }
            // union pts
            //SVFUtil::outs() << "aaa8"   <<"\n";
            //changed = unionPts(dstID, tmpDstPts);
            changed = unionPts(dstID, srcID);
        }else if(const CallBase *CB = llvm::dyn_cast<CallBase>(inst)){
            PointsTo tmpDstPts;
            bool dycFlag = false;
            Function *calledFunction = CB->getCalledFunction();
            if(calledFunction && (calledFunction->getName() == "__dynamic_cast")){
                
                //llvm::Value *sourceObject = CB->getArgOperand(0); // get pagNode
                //Type * srcType = sourceObject->getType()->isPointerTy() ? sourceObject->getType()->getPointerElementType() : sourceObject->getType();
                // std::string str4;
                // llvm::raw_string_ostream rso4(str4);
                // sourceObject->print(rso4);
                // rso4.flush();
                // std::cout << "eeeuuuw66:" <<str4 << std::endl;
                //  %316 = tail call i8* @__dynamic_cast(i8* nonnull %1, i8* bitcast ({ i8*, i8* }* @_ZTI9BaseClass to i8*), i8* bitcast ({ i8*, i8*, i8* }* @_ZTI5Right to i8*), i64 0) #15, !dbg !1493

                if (llvm::ConstantExpr* CE = llvm::dyn_cast<llvm::ConstantExpr>(CB->getArgOperand(2))) {
                    if (CE->getOpcode() == Instruction::BitCast) {
                        Value* targetTypeInfo = CE->getOperand(0);
                        // Now proceed further with targetTypeInfo.
                        if (llvm::GlobalVariable *GV = llvm::dyn_cast<llvm::GlobalVariable>(targetTypeInfo)) {
                            
                            llvm::StringRef destName = GV->getName();  //get dest type info
                            
                            //std::cout << "dstNamr:" <<destName.str() << std::endl;
                            
                            std::string DemangledName = llvm::demangle(destName.str());
                            
                            //std::cout << "dstNamrRTTI:" <<DemangledName << std::endl;
                            //"typeinfo for"
                            string className = "";
                            const string rttiLabelAfterDemangle = "typeinfo for ";
                            if (DemangledName.compare(0, rttiLabelAfterDemangle.size(),
                                rttiLabelAfterDemangle) == 0)
                            {
                                className = DemangledName.substr(rttiLabelAfterDemangle.size());
                                //std::cout << "dstNamrRTTI:" <<className << std::endl;
                            }

                            //we get the target className ,then we get the type from name2Struct
                            //then we get the parent class set from fld2Class
                            //then check the object in ptrVir,
                            //if we can get the target type, that will be ok ,and we will get the offset from struct2subFld
                            // then we create a subobject with this offset.
                            Type * dynamicType = name2Struct[className];
                            for(NodeID o : srcPts){
                                //we need to consider if field sensitive? 
                                //if field insensitive,just copy type and do nothing
                                //else do this thing
                                 //we should not check field sensitive here 
                                //the ptrVir's object is not base
                                //we should not use base
                                bool baseFlag = false;
                                   
                                NodeID baseId = getBaseObjVar(o);
                                //std::cout << "base:"<< getPAG()->getGNode(baseId)->toString() <<"\n";
                                auto iterBaseObj = ptrVir.find(baseId);  //if can not find in ptrVir, it indicate that the object o should not exist in the dst pts
                                                                //only when the object and the exist in ptrVir, we add it to dst pts.
                                                                //else we won't add it to the dst pts.

                                                                //shall we update ptrVir here due to dynamic?
                                                                //we should not due to that the object only init in costructor
                                                                //ptrVir also should contain srcType
                                // std::string str0;
                                // llvm::raw_string_ostream rso0(str0);
                                // srcType->print(rso0);
                                // rso0.flush();
                                // std::cout << "srcType:"<< str0 << "\n";

                                // std::string str1;
                                // llvm::raw_string_ostream rso1(str1);
                                // dynamicType->print(rso1);
                                // rso1.flush();
                                // std::cout << "dynamicType:"<< str1 << "\n";



                                
                                if(iterBaseObj  != ptrVir.end()){
                                    for(const auto& virTypeKey: iterBaseObj->second){
                                        
                                        // std::string str2;
                                        // llvm::raw_string_ostream rso2(str2);
                                        // virTypeKey.first->print(rso2);
                                        // rso2.flush();
                                        // std::cout << "firstType:"<< str2 << "\n";
                                        
                                        
                                        if(virTypeKey.second.find(dynamicType) != virTypeKey.second.end()){
                                            //we should check field sensitive here.
                                            //const auto &iterSubKey = struct2subFld[dynamicType];
                                            baseFlag = true;

                                            bool fldIn = isFieldInsensitive(o);

                                            // std::string str2;
                                            // llvm::raw_string_ostream rso2(str2);
                                            // virTypeKey.first->print(rso2);
                                            // rso2.flush();
                                            // std::cout << "virTypeKey.first:"<< str2 << "\n";

                                            if(!fldIn){

                                                auto& setOff = struct2subFld[virTypeKey.first][dynamicType];   //may happen different type same offset
                                                
                                                // create object
                                                //getGepObjVar to change 
                                                //check if the object exist or create a new one.
                                                //we make this object like a gep object actually it is not the type
                                                //the problem at here is that it will be ok to use addGepObjNode?
                                                //the best way to create the obj is that, we make the create copy obj.
                                                //the dynamic is kind of gep inst
                                                //check the object o offset
                                                
                                                
                                                //std::cout << "offseta11:" << offset  <<"\n"; 
                                                //std::cout << "offseta222:" << getGepObja(o)->getLocationSet().getFldOff()  <<"\n"; 
                                                for(auto t_off : setOff){
                                                    //std::cout << "offsetaaa:" << offset + t_off <<"\n"; 
                                                    NodeID dynPtdNode = getDynamicObjVar(baseId, t_off);
                                                    //here we just add type, not do fileter out.
                                                    addType2ptrNodeUniq(dynPtdNode, srcID, dstID, dynamicType);
                                                    tmpDstPts.set(dynPtdNode);


                                                    // std::cout << "points-to:::::"<< getPAG()->getGNode(dynPtdNode)->toString() <<"\n";
                                                    // s32_t offset111 = 0;    
                                                    // NodeID baseId111 = getBaseObjVar(dynPtdNode);
                                                    // std::cout << "o:" << o <<"\n";
                                                    // std::cout << "dynPtdNode:" << dynPtdNode <<"\n";
                                                    // if(baseId111 != dynPtdNode){
                                                    //     GepObjVar* gep_o111 =  getGepObja(dynPtdNode);
                                                    //     offset111 = gep_o111->getLocationSet().getFldOff();
                                                    //     std::cout << "--offsetaaa:" << offset111 <<"\n"; 
                                                    // }
                                                    // std::cout << "offset:" << offset111 <<"\n"; 
                                                    //std::cout << "offseggt:" << getGepObja(dynPtdNode)->getLocationSet().getFldOff() <<"\n";

                                                }
                                            }else{
                                                //just copy type,as usual copy 
                                                //we should not do anything else.
                                                //and we should only add struct type
                                                addType2ptrNodeUniq(o, srcID, dstID, dynamicType);
                                                tmpDstPts.set(o);
                                            }
                                            
                                            

                                        }
                                    }
                                }else{
                                    //the object should filter out and we do nothing.
                                }

                                if(!baseFlag){
                                    auto iterObj = ptrVir.find(o);  //if can not find in ptrVir, it indicate that the object o should not exist in the dst pts
                                                                //only when the object and the exist in ptrVir, we add it to dst pts.
                                                                //else we won't add it to the dst pts.

                                                                //shall we update ptrVir here due to dynamic?
                                                                //we should not due to that the object only init in costructor
                                                                //ptrVir also should contain srcType
                                    // std::string str0;
                                    // llvm::raw_string_ostream rso0(str0);
                                    // srcType->print(rso0);
                                    // rso0.flush();
                                    // std::cout << "srcType:"<< str0 << "\n";

                                    std::string str1;
                                    llvm::raw_string_ostream rso1(str1);
                                    dynamicType->print(rso1);
                                    rso1.flush();
                                    std::cout << "dynamicType:"<< str1 << "\n";

                                    
                                    if(iterObj  != ptrVir.end()){
                                        for(const auto& virTypeKey: iterObj->second){
                                            
                                            
                                            if(virTypeKey.second.find(dynamicType) != virTypeKey.second.end()){
                                                //we should check field sensitive here.
                                                //const auto &iterSubKey = struct2subFld[dynamicType];
                                                
                                                bool fldIn = isFieldInsensitive(o);

                                                std::string str2;
                                                llvm::raw_string_ostream rso2(str2);
                                                virTypeKey.first->print(rso2);
                                                rso2.flush();
                                                std::cout << "virTypeKey.first:"<< str2 << "\n";

                                                if(!fldIn){

                                                    auto& setOff = struct2subFld[virTypeKey.first][dynamicType];   //may happen different type same offset
                                                    //only the zero object should be create
                                                    //and the type of offset zero should be add.
                                                    // create object
                                                    //getGepObjVar to change 
                                                    //check if the object exist or create a new one.
                                                    //we make this object like a gep object actually it is not the type
                                                    //the problem at here is that it will be ok to use addGepObjNode?
                                                    //the best way to create the obj is that, we make the create copy obj.
                                                    //the dynamic is kind of gep inst
                                                    //check the object o offset
                                                    s32_t offset = 0;    
                                                    NodeID baseId = getBaseObjVar(o);
                                                    if(baseId != o){
                                                        GepObjVar* gep_o =  getGepObja(o);
                                                        offset = gep_o->getLocationSet().getFldOff();
                                                    }
                                                    for(auto t_off : setOff){
                                                        NodeID dynPtdNode =getDynamicObjVar(o, offset + t_off);
                                                        //here we just add type, not do fileter out.
                                                        addType2ptrNodeUniq(dynPtdNode, srcID, dstID, dynamicType);
                                                        tmpDstPts.set(dynPtdNode);
                                                    }
                                                }else{
                                                    //just copy type,as usual copy 
                                                    //we should not do anything else.
                                                    //and we should only add struct type
                                                    addType2ptrNodeUniq(o, srcID, dstID, dynamicType);
                                                    tmpDstPts.set(o);
                                                }
                                                
                                                

                                            }
                                        }
                                    }else{
                                        //the object should filter out and we do nothing.
                                    }
                                }
                                
                                
                                
                            }

                            //here to unionPts
                            changed =  unionPts(dstID, tmpDstPts);
                            dycFlag  = true;

                        }
                        
                        //get the first argment pointer
                        //get the pointer points to object
                        //check the typeof

                        // std::string str0;
                        // llvm::raw_string_ostream rso0(str0);
                        // CE->print(rso0);
                        // rso0.flush();
                        // std::cout << "aaawww66inst:" <<str0 << std::endl;

                        // std::string str5;
                        // llvm::raw_string_ostream rso5(str5);
                        // targetTypeInfo->print(rso5);
                        // rso5.flush();
                        // std::cout << "aaawww66:" <<str5 << std::endl;


                    }

                }


                 
            }
            if(!dycFlag){
                changed = unionPts(dstID, srcID);
                //just copy type info do nothing?
                for(NodeID o : srcPts){  //here error
                    copyTypePAGUniq(o, srcID, dstID);
                }
            }

        }
        else{
            // std::string instStr;
            // llvm::raw_string_ostream instSS(instStr);
            // instSS << (*inst);
            //SVFUtil::outs() << "copy instruction: " << instStr << "\n";
            // union pts
            //SVFUtil::outs() << "aaa9"   <<"\n";
            changed = unionPts(dstID, srcID);
            //just copy type info do nothing?
            for(NodeID o : srcPts){  //here error
                copyTypePAGUniq(o, srcID, dstID);
            }
            
                
        }
 
    }else{
        //union the pts.
        //SVFUtil::outs() << "aaa10"   <<"\n";
        changed = unionPts(dstID, srcID);
        //still need to copy type
        for(NodeID o : srcPts){  //here error
            copyTypePAGUniq(o, srcID, dstID);
        }
    }


    double end = stat->getClk();
    copyTime += (end - start) / TIMEINTERVAL;

    const PointsTo& tmpAddPts = getPts(dstID);
    allObj |= tmpAddPts; 

    return changed;


}





//the effective of this work is the most important
//we may need to make it faster
//the work of this fun should only consider about add function, not other things

int FlowSensitiveStruct::addType(NodeID baseId, llvm::Type* dstType, s32_t offset, int srcIdx, int dstIdx) {
    std::set<pair<Type*, s32_t>> tmpType;
    //SVFUtil::outs() << "type1" << "\n";
    // Get iterator to baseId's entry in typeSet
    auto baseIdIt = typeSet.find(baseId);
    if (baseIdIt != typeSet.end()) {  //can be find means the object exist in typeSet
        if (srcIdx != -1) {
            auto idxSrcIt = baseIdIt->second.find(srcIdx);
            if (idxSrcIt != baseIdIt->second.end()) {
                tmpType = idxSrcIt->second;
            }
        }

        if (dstIdx != -1) {
            auto idxDstIt = baseIdIt->second.find(dstIdx);
            if (idxDstIt != baseIdIt->second.end()) {
                tmpType.insert(idxDstIt->second.begin(), idxDstIt->second.end());
            }
        }
        if (dstType != nullptr) {
            tmpType.emplace(dstType, offset); // Using emplace instead of make_pair + insert
        }else{
            //SVFUtil::outs() << "type null" << "\n"; //we may should return -1 or something at here.
        }  
        // Check if this set exists already
        for (const auto& idxKey : baseIdIt->second) {
            if (tmpType == idxKey.second) {
                return idxKey.first; // Early return
            }
        }
        // If we reached here, the set doesn't exist. Insert and return new index.
        int newSize = baseIdIt->second.size();
        baseIdIt->second[newSize] = tmpType;
        return newSize;
    }else{  //this means that the object not exist in typeSet
        typeSet[baseId][0].emplace(make_pair(dstType, offset));
        return 0;
    }


}







//we should only add type which is struct
//we have to check if this function also guranteen that the type copy at the same time.
//this fun also copy type set to dst 
void FlowSensitiveStruct::addType2ptrNodeUniq(NodeID object, NodeID srcID, NodeID dstID, llvm::Type* destType) {
    s32_t offset = 0;
    NodeID baseId = getBaseObjVar(object);
    if (baseId != object) {
        GepObjVar* gep_o = getGepObja(object);
        offset = gep_o->getLocationSet().getFldOff();
    }
    auto keyBaseDst = make_pair(baseId, dstID);
    auto keyBaseSrc = make_pair(baseId, srcID);
    auto itrBaseDst = ptrNode2T.find(keyBaseDst);
    auto itrBaseSrc = ptrNode2T.find(keyBaseSrc);

    if (itrBaseDst == ptrNode2T.end()) { // dst not exist

        if (itrBaseSrc == ptrNode2T.end()) { // src not exist

            ptrNode2T[keyBaseDst] = addType(baseId, destType, offset, -1, -1);
            //SVFUtil::outs() << "add6-" << "\n";
        } else {  //src exist
            //SVFUtil::outs() << "add7" << "\n";
            int idx = itrBaseSrc->second;

            // Use a reference here
            auto& typeKey = typeSet[baseId][idx];
            //SVFUtil::outs() << "add8" << "\n";
            if (typeKey.find(make_pair(destType, offset)) == typeKey.end()) {  //in src can not find destType
                //SVFUtil::outs() << "add9" << "\n";
                ptrNode2T[keyBaseDst] = addType(baseId, destType, offset, idx, -1);
                //SVFUtil::outs() << "add9-" << "\n";
            } else {  //in src can find destType
                //SVFUtil::outs() << "add10" << "\n";
                ptrNode2T[keyBaseDst] = idx;
            }
            //SVFUtil::outs() << "add8-" << "\n";
        }
    } else { // dst exist
        //SVFUtil::outs() << "add18" << "\n";
        int idxDst = itrBaseDst->second;

        // Use a reference here too
        auto& typeKeyDst = typeSet[baseId][idxDst];
        //SVFUtil::outs() << "add23" << "\n";
        if (itrBaseSrc != ptrNode2T.end()) { // src exist
            int idxSrc = itrBaseSrc->second;
            //SVFUtil::outs() << "add28" << "\n";
            if (idxSrc != idxDst) {  //srcIdx not equal dstIdx,we should merger and add type
                //SVFUtil::outs() << "add231" << "\n";
                ptrNode2T[keyBaseDst] = addType(baseId, destType, offset, idxSrc, idxDst);
                //SVFUtil::outs() << "add231" << "\n";
            } else { // srcIdx == dstIdx
                //SVFUtil::outs() << "add23ff1-" << "\n";
                if (typeKeyDst.find(make_pair(destType, offset)) == typeKeyDst.end()) {
                    ptrNode2T[keyBaseDst] = addType(baseId, destType, offset, idxDst, -1);
                }
                //SVFUtil::outs() << "add23ff1" << "\n";
            }
            //SVFUtil::outs() << "add28-" << "\n";
        } else { // src not exist
            //SVFUtil::outs() << "add218-" << "\n";
            if (typeKeyDst.find(make_pair(destType, offset)) == typeKeyDst.end()) {
                ptrNode2T[keyBaseDst] = addType(baseId, destType, offset, idxDst, -1);
            }
            //SVFUtil::outs() << "add218-jjj" << "\n";
        }
    }
}








void FlowSensitiveStruct::copyTypePAGUniq(NodeID object, NodeID srcID, NodeID dstID) {
    NodeID baseId = getBaseObjVar(object);
    
    auto keyBaseDst = make_pair(baseId, dstID);
    auto keyBaseSrc = make_pair(baseId, srcID);
    
    auto itrBaseDst = ptrNode2T.find(keyBaseDst);
    auto itrBaseSrc = ptrNode2T.find(keyBaseSrc);

    // If dstID doesn't exist in the map
    if (itrBaseDst == ptrNode2T.end()) {
        // If srcID exists in the map, copy its value to dstID
        if (itrBaseSrc != ptrNode2T.end()) {
            ptrNode2T[keyBaseDst] = itrBaseSrc->second;
        }
    } else {
        // If both dstID and srcID exist in the map and they're not pointing to the same index
        if (itrBaseSrc != ptrNode2T.end() && itrBaseDst->second != itrBaseSrc->second) {
            ptrNode2T[keyBaseDst] = addType(baseId, nullptr, 0, itrBaseDst->second, itrBaseSrc->second);
        }
    }
}





void FlowSensitiveStruct::copyTypePAG2SVFGUniq(NodeID object, NodeID srcID, NodeID loc, NodeID ptd) {
    NodeID baseId = getBaseObjVar(object);
    
    auto baseSrcKey = make_pair(baseId, srcID);
    auto itrBaseSrc = ptrNode2T.find(baseSrcKey);

    if (itrBaseSrc != ptrNode2T.end()) {
        int idxPAG = itrBaseSrc->second;
        auto locPtdKey = make_pair(loc, ptd);

        auto& baseMap = inType[baseId]; // Directly access or create the inner map
        auto itrLocPtd = baseMap.find(locPtdKey);

        if (itrLocPtd != baseMap.end()) {
            int idxSVFG = itrLocPtd->second;
            if (idxSVFG != idxPAG) {
                baseMap[locPtdKey] = addType(baseId, nullptr, 0, idxSVFG, idxPAG);
            }
        } else {
            baseMap[locPtdKey] = idxPAG;
        }
    }
}







void FlowSensitiveStruct::copyTypeSVFGUniq(NodeID object, NodeID srcLoc, NodeID srcPtd, NodeID dstLoc, NodeID dstPtd) {
    NodeID baseId = getBaseObjVar(object);
    
    auto baseItr = inType.find(baseId);
    if (baseItr != inType.end()) {
        auto srcKey = make_pair(srcLoc, srcPtd);
        auto srcItr = baseItr->second.find(srcKey);
        
        if (srcItr != baseItr->second.end()) {
            int idxSrc = srcItr->second;
            
            auto dstKey = make_pair(dstLoc, dstPtd);
            auto dstItr = baseItr->second.find(dstKey);

            if (dstItr != baseItr->second.end()) {
                if (dstItr->second != idxSrc) {
                    baseItr->second[dstKey] = addType(baseId, nullptr, 0, idxSrc, dstItr->second);
                }
            } else {
                baseItr->second[dstKey] = idxSrc;
            }
        }
    }
}






void FlowSensitiveStruct::copyTypeSVFG2PAGUniq(NodeID object, NodeID dstID, NodeID loc, NodeID ptd) {
    NodeID baseId = getBaseObjVar(object);
    
    // Check if type exists in inType
    auto baseItr = inType.find(baseId);
    if (baseItr != inType.end()) {
        auto locPtdKey = make_pair(loc, ptd);
        auto locPtdItr = baseItr->second.find(locPtdKey);
        
        if (locPtdItr != baseItr->second.end()) {
            int idxSVFG = locPtdItr->second;
            
            auto baseDstKey = make_pair(baseId, dstID);
            auto baseDstItr = ptrNode2T.find(baseDstKey);
            
            // If exists in ptrNode2T
            if (baseDstItr != ptrNode2T.end()) {
                if (baseDstItr->second != idxSVFG) {
                    ptrNode2T[baseDstKey] = addType(baseId, nullptr, 0, idxSVFG, baseDstItr->second);
                }
            } else {
                ptrNode2T[baseDstKey] = idxSVFG;
            }
        }
    }
}




bool FlowSensitiveStruct::checkGepInst(NodeID object, NodeID srcID, s32_t offset){
    NodeID baseId = getBaseObjVar(object);
    s32_t objOff = 0;
    if(baseId != object){
        GepObjVar* gep_o =  getGepObja(object);
        objOff = gep_o->getLocationSet().getFldOff();
    }
    auto keyBaseSrc = make_pair(baseId, srcID);
    auto itrBaseSrc = ptrNode2T.find(keyBaseSrc);
    if(itrBaseSrc != ptrNode2T.end()){
        int idx = itrBaseSrc->second;
        const auto& typeSetKey = typeSet[baseId][idx];
        for(const auto & typePair : typeSetKey){
            if(typePair.second == objOff){
                const auto& subTypeKey = allStruct2FldOff[typePair.first];
                if(subTypeKey.find(offset) != subTypeKey.end()){
                    return true;
                }else if(heapObjFlag.find(baseId) != heapObjFlag.end()){
                    auto iterAli = allStructAlig.find(typePair.first);
                    if(iterAli != allStructAlig.end()){
                        int mod_off = offset % iterAli->second;
                        if(subTypeKey.find(mod_off) != subTypeKey.end()){
                            return true;
                        }
                    }
                    
                }
            }
            
        }
    }else{
        
        return true;
        
    }
    return false;
}




bool FlowSensitiveStruct::updateCallGraph(const CallSiteToFunPtrMap& callsites)
{
    double start = stat->getClk();
    CallEdgeMap newEdges;
    //SVFUtil::outs() << "updateCallGraph:333"  << "\n";
    onTheFlyCallGraphSolve(callsites, newEdges,false);
    //SVFUtil::outs() << "updateCallGraph444:"  << "\n";
    // Bound the new edges by the Andersen's call graph.
    // TODO: we want this to be an assertion eventually.
    const CallEdgeMap &andersCallEdgeMap = ander->getIndCallMap();
    for (typename CallEdgeMap::value_type &csfs : newEdges)
    {
        const CallICFGNode *potentialCallSite = csfs.first;
        FunctionSet &potentialFunctionSet = csfs.second;

        // Check this callsite even calls anything per Andersen's.
        typename CallEdgeMap::const_iterator andersFunctionSetIt
            = andersCallEdgeMap.find(potentialCallSite);
        if (andersFunctionSetIt == andersCallEdgeMap.end())
        {
            potentialFunctionSet.clear();
        }

        const FunctionSet &andersFunctionSet = andersFunctionSetIt->second;
        for (FunctionSet::iterator potentialFunctionIt = potentialFunctionSet.begin();
                potentialFunctionIt != potentialFunctionSet.end(); )
        {
            const SVFFunction *potentialFunction = *potentialFunctionIt;
            if (andersFunctionSet.find(potentialFunction) == andersFunctionSet.end())
            {
                // potentialFunction is not in the Andersen's call graph -- remove it.
                potentialFunctionIt = potentialFunctionSet.erase(potentialFunctionIt);
            }
            else
            {
                // potentialFunction is in the Andersen's call graph -- keep it..
                ++potentialFunctionIt;
            }
        }
    }

    SVFGEdgeSetTy svfgEdges;
    connectCallerAndCallee(newEdges, svfgEdges);

    updateConnectedNodes(svfgEdges);

    double end = stat->getClk();
    updateCallGraphTime += (end - start) / TIMEINTERVAL;
    return (!newEdges.empty());
}



