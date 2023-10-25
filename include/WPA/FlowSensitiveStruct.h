//===- FlowSensitiveStruct.h -- flow-sensitive type filter ----------------//

/*
 * FlowSensitiveStruct.h
 *
 *  Created on: Oct 08, 2019
 *      Author: Mohamad Barbar
 */

#ifndef FLOWSENSITIVETYPEFILTER_H_
#define FLOWSENSITIVETYPEFILTER_H_



#include "FastCluster/fastcluster.h"
#include "Graphs/SVFGOPT.h"
#include "MemoryModel/PointerAnalysisImpl.h"
#include "MSSA/SVFGBuilder.h"
#include "WPA/WPAFSSolver.h"
#include "WPA/FlowSensitive.h"
// #include "Util/SVFBasicTypes.h"

// #include "llvm/IR/Instruction.h"
// #include "llvm/IR/Instructions.h"

namespace SVF
{

class SVFModule;

/*!
 * Flow sensitive whole program pointer analysis with type-based heap cloning.
 */
class FlowSensitiveStruct : public FlowSensitive
{
public:
    /// Returns raw ctir metadata of the instruction behind a SVFG node.
    /// Wraps getRawCTirMetadata(const Value *). Returns null if it doesn't exist.
    // static const MDNode *getRawCTirMetadata(const SVFGNode *);

    /// Constructor
    //这里需要在BVDataPTAImpl construct中添加相应的FSSTRUCT_WPA类型
    //还需要对FSSTRUCT_WPA进行预定义
    FlowSensitiveStruct(PAG* _pag, PTATY type = FSSPARSE_WPA) : FlowSensitive(_pag, type){
        
    }

    /// Destructor
    virtual ~FlowSensitiveStruct() { };

    /// Flow sensitive analysis with FSTBHC.
    virtual void analyze() override;
    /// Initialize analysis.
    virtual void initialize() override;
    /// Finalize analysis.
    virtual void finalize() override;

    /// Get PTA name
    //这个还需要查明
    virtual const std::string PTAName() const override
    {
        return "FSTBHC";
    }

    /// For LLVM RTTI.
    static inline bool classof(const FlowSensitiveStruct *)
    {
        return true;
    }

    /// For LLVM RTTI.
    //这里也需要查明
    static inline bool classof(const PointerAnalysis *pta)
    {
        return pta->getAnalysisTy() == FSSPARSE_WPA;
    }

    virtual bool propAlongIndirectEdge(const IndirectSVFGEdge* edge) override;
    virtual bool propAlongDirectEdge(const DirectSVFGEdge* edge) override;
    
    virtual bool propVarPtsFromSrcToDst(NodeID var, const SVFGNode* src, const SVFGNode* dst);

    /// Propagate points-to information from an actual-param to a formal-param.
    /// Not necessary if SVFGOPT is used instead of original SVFG.
    virtual bool propagateFromAPToFP(const ActualParmSVFGNode* ap, const SVFGNode* dst);
    /// Propagate points-to information from a formal-ret to an actual-ret.
    /// Not necessary if SVFGOPT is used instead of original SVFG.
    virtual bool propagateFromFRToAR(const FormalRetSVFGNode* fr, const SVFGNode* dst);

    //addr需要修改
    virtual bool processAddr(const AddrSVFGNode* addr) override;
    virtual bool processGep(const GepSVFGNode* gep) override;
    virtual bool processLoad(const LoadSVFGNode* load) override;
    virtual bool processStore(const StoreSVFGNode* store) override;
    virtual bool processPhi(const PHISVFGNode* phi) override;
    virtual bool processCopy(const CopySVFGNode* copy) override;


    virtual bool updateCallGraph(const CallSiteToFunPtrMap& callsites);
    //我们先让其可以编译通过，再处理别的事情
    //添加我们自己要处理的指令类型
    //这里还缺少相应的节点类型的支持,比如
    //cast不过是特殊类型的copy，所以我们只需要在处理copy时进行判断即可
    //array是特殊的类型的gep指令，所以，在处理array时只需要在gep指令中添加判断即可
    //subtype这里涉及到多条指令，可能需要考虑gep和cast两条语句得组合就和phi指令类似
    //construct语句需要特殊处理，这是一个单独的函数，我们需要对这种函数特殊处理，这并不能算是一个节点，但是这里涉及到识别构造函数，我想这件事情是容易的
    //dynamic_cast同样是一个函数，我们只需要特殊识别这个函数即可，但是这里需要单独处理。
    //subtype可以在cast中识别。
    // virtual bool processCast(const CopySVFGNode* copy) override;
    // virtual bool processArray(const CopySVFGNode* copy) override;
    // virtual bool processField(const CopySVFGNode* copy) override;
    //这里涉及到专有函数的问题
    // virtual bool processSubtype(const CopySVFGNode* copy) override { return false;}
    // virtual bool processConstruct(const CopySVFGNode* copy) override {return false;}
    // virtual bool processDynamic(const CopySVFGNode* copy) override {return false;}

    void addType2ptrNodeUniq(NodeID object, NodeID srcID,NodeID dstID, llvm::Type* destType);

    void copyTypePAGUniq(NodeID object, NodeID srcID,NodeID dstID);
    void copyTypePAG2SVFGUniq(NodeID object, NodeID srcID, NodeID loc, NodeID ptd);
    void copyTypeSVFG2PAGUniq(NodeID object, NodeID dstID, NodeID loc, NodeID ptd);
    void copyTypeSVFGUniq(NodeID object, NodeID srcLoc, NodeID srcPtd, NodeID dstLoc, NodeID dstPtd);

    //void mergeTypeSet(NodeID baseId,NodeID dstID, int sizeSrc, int sizeDst)
    //inline const NodeBS& getAllFieldsObjNode(NodeID id);
    int addType(NodeID baseId, llvm::Type* dstType , s32_t offset, int idx1, int idx2);

    bool checkGepInst(NodeID object, NodeID srcID, s32_t offset);
    //bool checkClassType(NodeID srcId, NodeID object, llvm::Type *type);
    // virtual inline bool updateInFromIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) override;
    // virtual inline bool updateInFromOut(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) override;

    // virtual inline bool unionPtsFromIn(const SVFGNode* stmt, NodeID srcVar, NodeID dstVar) override;
    // virtual inline bool unionPtsFromTop(const SVFGNode* stmt, NodeID srcVar, NodeID dstVar) override;

    // virtual inline bool propDFOutToIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) override;
    // virtual inline bool propDFInToIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) override;

    // virtual void expandFIObjs(const PointsTo& pts, PointsTo& expandedPts) override;

    /// Extracts the value from SVFGNode (if it exists), and calls
    /// getTypeFromCTirMetadata(const Value *).
    /// If no ctir type exists, returns null (void).
    // const DIType *getTypeFromCTirMetadata(const SVFGNode *);

protected:
    // void backPropagate(NodeID clone);


private:
    /// Determines whether each GEP is for a load or not. Builds gepIsLoad map.
    /// This is a quick heuristic; if all destination nodes are loads, it's a load.
    void determineWhichGepsAreLoads(void);

    /// Returns true if the given GEP is for loads, false otherwise. If the node ID
    /// is not for a GEP SVFG node, returns false.
    bool gepIsLoad(NodeID gep);

    /// Whether to allow for reuse at stores.
    bool storeReuse;
    /// Whether to allow reuse at all instructions (load/store/field).
    /// allReuse => storeReuse.
    bool allReuse;

    /// Maps GEP objects to the SVFG nodes that retrieved them with getGepObjClones.
    Map<NodeID, NodeBS> gepToSVFGRetrievers;
    /// Maps whether a (SVFG) GEP node is a load or not.
    NodeBS loadGeps;
    //object all type 
    //map<NodeID,map<int,map<Type*,int>>> typeSet;
    //map<NodeID,map<int,set<Type*>>> typeSet;
    std::unordered_map<NodeID,std::unordered_map<int,std::set<pair<Type*,s32_t>>>> typeSet;
    //map<NodeID,map<NodeID,int>> node2Type;
    std::unordered_map<pair<NodeID,NodeID>,int> ptrNode2T;
    //map<std::pair<object,ptr>,int> ptrNode2T
    //object also need max number of type 
    // and most aggresive way to do this work is to change the class MemObj
    //we also need struct to progate type info for indirect edge.
    //map<object, map<pair<loc,nodeid>,int>> inType
    //loc is svfgnode id
    //it comes the possible that one object from differenct path get the same store
    //we compare if the two idx eauql 
    //and then consider one set include another , if so use the one that longer
    //else consider to merger two set into one.
    std::unordered_map<NodeID , std::unordered_map<pair<NodeID,NodeID>,int> > inType;
    // 3 probelm:
    //1.type check is neceseary?
    //2.return may error
    //3.type ,we should consider element type , not pointer type.(important)
    // //here to consider about class with virtual function
    // //map<object,set<type>>  ptV
    // //not fully right
    // //a lot of error
    // //we also need the subClass
    // //map<NodeID,set<Type*>> ptrVir;
    // map<NodeID,map<Type*, set<Type*> >> ptrVir;
    
    //here to consider about type union
    //the better is that  we can easy to copy,but now the copy is also easy
    //the worse is that we need to check type
    //

    //now we are in the high site,we can consider every detail in our way.
    std::unordered_set<NodeID> heapObjFlag;

    //we also need some global value to account the number of every type of inst.
    
    //here to count the check meaning
    // int loadCheck = 0;  //we need to consider due to we need to check the object not pointer.
    // int retCheck = 0;
    // int paramCheck = 0;
    // int storeCheck = 0;  //this is very small
    // int addCheck = 0; //this seems never happen in check

    PointsTo allObj;
};

} // End namespace SVF

#endif /* FLOWSENSITIVETYPEFILTER_H_ */
