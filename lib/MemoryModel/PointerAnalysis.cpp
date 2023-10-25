//===- PointerAnalysis.cpp -- Base class of pointer analyses------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2017>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * PointerAnalysis.cpp
 *
 *  Created on: May 14, 2013
 *      Author: Yulei Sui
 */

#include "Util/Options.h"
#include "SVF-FE/CallGraphBuilder.h"
#include "SVF-FE/CHGBuilder.h"
#include "SVF-FE/DCHG.h"
#include "SVF-FE/LLVMUtil.h"
#include "SVF-FE/CPPUtil.h"
#include "Util/SVFModule.h"
#include "Util/SVFUtil.h"
#include "SVF-FE/LLVMUtil.h"

#include "MemoryModel/PointerAnalysisImpl.h"
#include "MemoryModel/PAGBuilderFromFile.h"
#include "MemoryModel/PTAStat.h"
#include "Graphs/ThreadCallGraph.h"
#include "Graphs/ICFG.h"

#include <iomanip>
#include <iostream>
#include <fstream>
#include <sstream>

using namespace SVF;
using namespace SVFUtil;
using namespace cppUtil;
using namespace LLVMUtil;


SVFIR* PointerAnalysis::pag = nullptr;

const std::string PointerAnalysis::aliasTestMayAlias            = "MAYALIAS";
const std::string PointerAnalysis::aliasTestMayAliasMangled     = "_Z8MAYALIASPvS_";
const std::string PointerAnalysis::aliasTestNoAlias             = "NOALIAS";
const std::string PointerAnalysis::aliasTestNoAliasMangled      = "_Z7NOALIASPvS_";
const std::string PointerAnalysis::aliasTestPartialAlias        = "PARTIALALIAS";
const std::string PointerAnalysis::aliasTestPartialAliasMangled = "_Z12PARTIALALIASPvS_";
const std::string PointerAnalysis::aliasTestMustAlias           = "MUSTALIAS";
const std::string PointerAnalysis::aliasTestMustAliasMangled    = "_Z9MUSTALIASPvS_";
const std::string PointerAnalysis::aliasTestFailMayAlias        = "EXPECTEDFAIL_MAYALIAS";
const std::string PointerAnalysis::aliasTestFailMayAliasMangled = "_Z21EXPECTEDFAIL_MAYALIASPvS_";
const std::string PointerAnalysis::aliasTestFailNoAlias         = "EXPECTEDFAIL_NOALIAS";
const std::string PointerAnalysis::aliasTestFailNoAliasMangled  = "_Z20EXPECTEDFAIL_NOALIASPvS_";

/*!
 * Constructor
 */
PointerAnalysis::PointerAnalysis(SVFIR* p, PTATY ty, bool alias_check) :
    svfMod(nullptr),ptaTy(ty),stat(nullptr),ptaCallGraph(nullptr),callGraphSCC(nullptr),icfg(nullptr),chgraph(nullptr),typeSystem(nullptr)
{
    pag = p;
    OnTheFlyIterBudgetForStat = Options::StatBudget;
    print_stat = Options::PStat;
    ptaImplTy = BaseImpl;
    alias_validation = (alias_check && Options::EnableAliasCheck);
}

/*!
 * Destructor
 */
PointerAnalysis::~PointerAnalysis()
{
    destroy();
    // do not delete the SVFIR for now
    //delete pag;
}


void PointerAnalysis::destroy()
{
    delete ptaCallGraph;
    ptaCallGraph = nullptr;

    delete callGraphSCC;
    callGraphSCC = nullptr;

    delete stat;
    stat = nullptr;

    delete chgraph;
    chgraph = nullptr;
}

/*!
 * Initialization of pointer analysis
 */
void PointerAnalysis::initialize()
{
    assert(pag && "SVFIR has not been built!");
    if (chgraph == nullptr)
    {
        CHGraph *chg = new CHGraph(pag->getModule());
        CHGBuilder builder(chg);
        builder.buildCHG();
        //builder.buildCHG(classNameSet);
        chgraph = chg;

    }

    svfMod = pag->getModule();

    /// initialise pta call graph for every pointer analysis instance
    if(Options::EnableThreadCallGraph)
    {
        ThreadCallGraph* cg = new ThreadCallGraph();
        ThreadCallGraphBuilder bd(cg, pag->getICFG());
        ptaCallGraph = bd.buildThreadCallGraph(pag->getModule());
    }
    else
    {
        PTACallGraph* cg = new PTACallGraph();
        CallGraphBuilder bd(cg,pag->getICFG());
        ptaCallGraph = bd.buildCallGraph(pag->getModule());
    }
    callGraphSCCDetection();

    // dump callgraph
    if (Options::CallGraphDotGraph)
        getPTACallGraph()->dump("callgraph_initial");

    
    //std::cout << "getClass2Name" << std::endl;
    getClassWithV();
    //std::cout << "good0" << std::endl;
    getClass2Name();
    //std::cout << "good11" << std::endl;
    getClassFld();
    //std::cout << "good12" << std::endl;
    getAllCTOR();
    //std::cout << "good3" << std::endl;
    getVptr2Vt();
    //std::cout << "good1" << std::endl;
    getArrType();
    getallStructFld();
    //printStructAndClass();
}


/*!
 * Return TRUE if this node is a local variable of recursive function.
 */
bool PointerAnalysis::isLocalVarInRecursiveFun(NodeID id) const
{
    const MemObj* obj = pag->getObject(id);
    assert(obj && "object not found!!");
    if(obj->isStack())
    {
        if(const Function* fun = pag->getGNode(id)->getFunction())
        {
            const SVFFunction* svffun = LLVMModuleSet::getLLVMModuleSet()->getSVFFunction(fun);
            return callGraphSCC->isInCycle(getPTACallGraph()->getCallGraphNode(svffun)->getId());
        }
    }
    return false;
}

/*!
 * Reset field sensitivity
 */
void PointerAnalysis::resetObjFieldSensitive()
{
    for (SVFIR::iterator nIter = pag->begin(); nIter != pag->end(); ++nIter)
    {
        if(ObjVar* node = SVFUtil::dyn_cast<ObjVar>(nIter->second))
            const_cast<MemObj*>(node->getMemObj())->setFieldSensitive();
    }
}

/*
 * Dump statistics
 */

void PointerAnalysis::dumpStat()
{

    if(print_stat && stat)
    {
        stat->performStat();
    }
}

/*!
 * Finalize the analysis after solving
 * Given the alias results, verify whether it is correct or not using alias check functions
 */
void PointerAnalysis::finalize()
{

    /// Print statistics
    dumpStat();

    /// Dump results
    if (Options::PTSPrint)
    {
        dumpTopLevelPtsTo();
        //dumpAllPts();
        //dumpCPts();
    }

    if (Options::TypePrint)
        dumpAllTypes();

    if(Options::PTSAllPrint)
        dumpAllPts();

    if (Options::FuncPointerPrint)
        printIndCSTargets();

    getPTACallGraph()->verifyCallGraph();

    if (Options::CallGraphDotGraph)
        getPTACallGraph()->dump("callgraph_final");

    if(!pag->isBuiltFromFile() && alias_validation)
        validateTests();

    if (!Options::UsePreCompFieldSensitive)
        resetObjFieldSensitive();
}

/*!
 * Validate test cases
 */
void PointerAnalysis::validateTests()
{
    validateSuccessTests(aliasTestMayAlias);
    validateSuccessTests(aliasTestNoAlias);
    validateSuccessTests(aliasTestMustAlias);
    validateSuccessTests(aliasTestPartialAlias);
    validateExpectedFailureTests(aliasTestFailMayAlias);
    validateExpectedFailureTests(aliasTestFailNoAlias);

    validateSuccessTests(aliasTestMayAliasMangled);
    validateSuccessTests(aliasTestNoAliasMangled);
    validateSuccessTests(aliasTestMustAliasMangled);
    validateSuccessTests(aliasTestPartialAliasMangled);
    validateExpectedFailureTests(aliasTestFailMayAliasMangled);
    validateExpectedFailureTests(aliasTestFailNoAliasMangled);
}


void PointerAnalysis::dumpAllTypes()
{
    for (OrderedNodeSet::iterator nIter = this->getAllValidPtrs().begin();
            nIter != this->getAllValidPtrs().end(); ++nIter)
    {
        const PAGNode* node = getPAG()->getGNode(*nIter);
        if (SVFUtil::isa<DummyObjVar>(node) || SVFUtil::isa<DummyValVar>(node))
            continue;

        outs() << "##<" << node->getValue()->getName().str() << "> ";
        outs() << "Source Loc: " << getSourceLoc(node->getValue());
        outs() << "\nNodeID " << node->getId() << "\n";

        Type* type = node->getValue()->getType();
        SymbolTableInfo::SymbolInfo()->printFlattenFields(type);
        if (PointerType* ptType = SVFUtil::dyn_cast<PointerType>(type))
            SymbolTableInfo::SymbolInfo()->printFlattenFields(getPtrElementType(ptType));
    }
}

/*!
 * Dump points-to of top-level pointers (ValVar)
 */
void PointerAnalysis::dumpPts(NodeID ptr, const PointsTo& pts)
{

    const PAGNode* node = pag->getGNode(ptr);
    /// print the points-to set of node which has the maximum pts size.
    if (SVFUtil::isa<DummyObjVar> (node))
    {
        outs() << "##<Dummy Obj > id:" << node->getId();
    }
    else if (!SVFUtil::isa<DummyValVar>(node) && !SVFModule::pagReadFromTXT())
    {
        if (node->hasValue())
        {
            outs() << "##<" << node->getValue()->getName().str() << "> ";
            outs() << "Source Loc: " << getSourceLoc(node->getValue());
        }
    }
    outs() << "\nPtr " << node->getId() << " ";

    if (pts.empty())
    {
        outs() << "\t\tPointsTo: {empty}\n\n";
    }
    else
    {
        outs() << "\t\tPointsTo: { ";
        for (PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit;
                ++it)
            outs() << *it << " ";
        outs() << "}\n\n";
    }

    outs() << "";

    for (PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit; ++it)
    {
        const PAGNode* node = pag->getGNode(*it);
        if(SVFUtil::isa<ObjVar>(node) == false)
            continue;
        NodeID ptd = node->getId();
        outs() << "!!Target NodeID " << ptd << "\t [";
        const PAGNode* pagNode = pag->getGNode(ptd);
        if (SVFUtil::isa<DummyValVar>(node))
            outs() << "DummyVal\n";
        else if (SVFUtil::isa<DummyObjVar>(node))
            outs() << "Dummy Obj id: " << node->getId() << "]\n";
        else
        {
            if (!SVFModule::pagReadFromTXT())
            {
                if (node->hasValue())
                {
                    outs() << "<" << pagNode->getValue()->getName().str() << "> ";
                    outs() << "Source Loc: "
                           << getSourceLoc(pagNode->getValue()) << "] \n";
                }
            }
        }
    }
}

/*!
 * Print indirect call targets at an indirect callsite
 */
void PointerAnalysis::printIndCSTargets(const CallICFGNode* cs, const FunctionSet& targets)
{
    outs() << "\nNodeID: " << getFunPtr(cs);
    outs() << "\nCallSite: ";
    outs() << SVFUtil::value2String(cs->getCallSite());
    outs() << "\tLocation: " << SVFUtil::getSourceLoc(cs->getCallSite());
    outs() << "\t with Targets: ";

    if (!targets.empty())
    {
        FunctionSet::const_iterator fit = targets.begin();
        FunctionSet::const_iterator feit = targets.end();
        for (; fit != feit; ++fit)
        {
            const SVFFunction* callee = *fit;
            outs() << "\n\t" << callee->getName();
        }
    }
    else
    {
        outs() << "\n\tNo Targets!";
    }

    outs() << "\n";
}

/*!
 * Print all indirect callsites
 */
void PointerAnalysis::printIndCSTargets()
{
    outs() << "==================Function Pointer Targets==================\n";
    const CallEdgeMap& callEdges = getIndCallMap();
    CallEdgeMap::const_iterator it = callEdges.begin();
    CallEdgeMap::const_iterator eit = callEdges.end();
    for (; it != eit; ++it)
    {
        const CallICFGNode* cs = it->first;
        const FunctionSet& targets = it->second;
        printIndCSTargets(cs, targets);
    }

    const CallSiteToFunPtrMap& indCS = getIndirectCallsites();
    CallSiteToFunPtrMap::const_iterator csIt = indCS.begin();
    CallSiteToFunPtrMap::const_iterator csEit = indCS.end();
    for (; csIt != csEit; ++csIt)
    {
        const CallICFGNode* cs = csIt->first;
        if (hasIndCSCallees(cs) == false)
        {
            outs() << "\nNodeID: " << csIt->second;
            outs() << "\nCallSite: ";
            outs() << SVFUtil::value2String(cs->getCallSite());
            outs() << "\tLocation: " << SVFUtil::getSourceLoc(cs->getCallSite());
            outs() << "\n\t!!!has no targets!!!\n";
        }
    }
}



/*!
 * Resolve indirect calls
 */
void PointerAnalysis::resolveIndCalls(const CallICFGNode* cs, const PointsTo& target, CallEdgeMap& newEdges)
{

    assert(pag->isIndirectCallSites(cs) && "not an indirect callsite?");
    /// discover indirect pointer target
    for (PointsTo::iterator ii = target.begin(), ie = target.end();
            ii != ie; ii++)
    {

        if(getNumOfResolvedIndCallEdge() >= Options::IndirectCallLimit)
        {
            wrnMsg("Resolved Indirect Call Edges are Out-Of-Budget, please increase the limit");
            return;
        }

        if(ObjVar* objPN = SVFUtil::dyn_cast<ObjVar>(pag->getGNode(*ii)))
        {
            const MemObj* obj = pag->getObject(objPN);

            if(obj->isFunction())
            {
                const Function* calleefun = SVFUtil::cast<Function>(obj->getValue());
                const SVFFunction* callee = getDefFunForMultipleModule(calleefun);

                /// if the arg size does not match then we do not need to connect this parameter
                /// even if the callee is a variadic function (the first parameter of variadic function is its paramter number)
                if(matchArgs(cs, callee) == false)
                    continue;

                if(0 == getIndCallMap()[cs].count(callee))
                {
                    newEdges[cs].insert(callee);
                    getIndCallMap()[cs].insert(callee);

                    ptaCallGraph->addIndirectCallGraphEdge(cs, cs->getCaller(), callee);
                    // FIXME: do we need to update llvm call graph here?
                    // The indirect call is maintained by ourself, We may update llvm's when we need to
                    //CallGraphNode* callgraphNode = callgraph->getOrInsertFunction(cs.getCaller());
                    //callgraphNode->addCalledFunction(cs,callgraph->getOrInsertFunction(callee));
                }
            }
        }
    }
}

/*!
 * Match arguments for callsite at caller and callee
 */
bool PointerAnalysis::matchArgs(const CallICFGNode* cs, const SVFFunction* callee)
{
    if(ThreadAPI::getThreadAPI()->isTDFork(cs->getCallSite()))
        return true;
    else
        return SVFUtil::getLLVMCallSite(cs->getCallSite()).arg_size() == callee->arg_size();
}

/*
 * Get virtual functions "vfns" based on CHA
 */
void PointerAnalysis::getVFnsFromCHA(const CallICFGNode* cs, VFunSet &vfns)
{
    if (chgraph->csHasVFnsBasedonCHA(SVFUtil::getLLVMCallSite(cs->getCallSite())))
        vfns = chgraph->getCSVFsBasedonCHA(SVFUtil::getLLVMCallSite(cs->getCallSite()));
}

/*
 * Get virtual functions "vfns" from PoninsTo set "target" for callsite "cs"
 */
//we get the object, but we do not have virtual table 
//and we do not get vptr map to the vtable.
//so we need to set the map between vptr and vtable
void PointerAnalysis::getVFnsFromPts(const CallICFGNode* cs, const PointsTo &target, VFunSet &vfns)
{

    if (chgraph->csHasVtblsBasedonCHA(SVFUtil::getLLVMCallSite(cs->getCallSite())))
    {
        Set<const GlobalValue*> vtbls;
        const VTableSet &chaVtbls = chgraph->getCSVtblsBasedonCHA(SVFUtil::getLLVMCallSite(cs->getCallSite()));
        for (PointsTo::iterator it = target.begin(), eit = target.end(); it != eit; ++it)
        {
            const PAGNode *ptdnode = pag->getGNode(*it);
            if (ptdnode->hasValue())
            {
                if (const GlobalValue *vtbl = SVFUtil::dyn_cast<GlobalValue>(ptdnode->getValue()))
                {
                    if (chaVtbls.find(vtbl) != chaVtbls.end())
                        vtbls.insert(vtbl);
                }
            }
        }
        chgraph->getVFnsFromVtbls(SVFUtil::getLLVMCallSite(cs->getCallSite()), vtbls, vfns);
    }
}

/*
 * Connect callsite "cs" to virtual functions in "vfns"
 */
void PointerAnalysis::connectVCallToVFns(const CallICFGNode* cs, const VFunSet &vfns, CallEdgeMap& newEdges)
{
    //// connect all valid functions
    for (VFunSet::const_iterator fit = vfns.begin(),
            feit = vfns.end(); fit != feit; ++fit)
    {
        const SVFFunction* callee = *fit;
        callee = getDefFunForMultipleModule(callee->getLLVMFun());
        if (getIndCallMap()[cs].count(callee) > 0)
            continue;
        if(SVFUtil::getLLVMCallSite(cs->getCallSite()).arg_size() == callee->arg_size() ||
                (SVFUtil::getLLVMCallSite(cs->getCallSite()).getFunctionType()->isVarArg() && callee->isVarArg()))
        {
            newEdges[cs].insert(callee);
            getIndCallMap()[cs].insert(callee);
            const CallICFGNode* callBlockNode = pag->getICFG()->getCallICFGNode(cs->getCallSite());
            ptaCallGraph->addIndirectCallGraphEdge(callBlockNode, cs->getCaller(),callee);
        }
    }
}

/// Resolve cpp indirect call edges
void PointerAnalysis::resolveCPPIndCalls(const CallICFGNode* cs, const PointsTo& target, CallEdgeMap& newEdges)
{
    assert(isVirtualCallSite(SVFUtil::getLLVMCallSite(cs->getCallSite())) && "not cpp virtual call");

    VFunSet vfns;
    if (Options::ConnectVCallOnCHA)
        getVFnsFromCHA(cs, vfns);
    else
        getVFnsFromPts(cs, target, vfns);
        //about virtual just change here will be ok
        //just set the vfns will be ok,the vfns is the function that get
        // but the "vfns" may also be a lot of functions, due to may be a lot of "target"
    connectVCallToVFns(cs, vfns, newEdges);
}

bool PointerAnalysis::checkArgTypesPointer(CallSite cs, const Function *fn)
{

    // here we skip the first argument (i.e., this pointer)
    u32_t arg_size = (fn->arg_size() > cs.arg_size()) ? cs.arg_size(): fn->arg_size();
    if(arg_size > 1)
    {
        for (unsigned i = 1; i < arg_size; i++)
        {
            auto cs_arg = cs.getArgOperand(i);
            auto fn_arg = fn->getArg(i);
            if (cs_arg->getType() != fn_arg->getType())
            {
                return false;
            }
        }
    }

    return true;
}



void PointerAnalysis::resolveVirCallbyType(const CallICFGNode* cs, CallEdgeMap& newEdges)
{
    assert(isVirtualCallSite(SVFUtil::getLLVMCallSite(cs->getCallSite())) && "not cpp virtual call");

    VFunSet vfns;
    
    const Instruction* csInst = cs->getCallSite();

    std::string str1;
    llvm::raw_string_ostream rso1(str1);
    csInst->print(rso1);
    rso1.flush();
    std::cout << "csInst:" <<str1 << std::endl;


    if (!chgraph->csHasVtblsBasedonCHA(SVFUtil::getLLVMCallSite(cs->getCallSite())))
        return;

    //const Instruction* csInst = cs->getCallSite();
    const llvm::CallInst* callInst = llvm::dyn_cast<llvm::CallInst>(csInst);
    if (!callInst){
        return;
    }

    llvm::Value* firstArg = callInst->getArgOperand(0);
    if(!firstArg){
        return;
    }
    if(!firstArg->getType()->isPointerTy()){
        return;
    }
    llvm::Type* vType = firstArg->getType()->getPointerElementType();
    

    std::string str10;
    llvm::raw_string_ostream rso10(str10);
    vType->print(rso10);
    rso10.flush();
    std::cout << "vType:"<< str10 << "\n";


    //assert(pag->hasValueNode(vptr));
    assert(pag->hasValueNode(firstArg));
    const PointsTo& target = getPts(pag->getValueNode(firstArg));


    // for(auto tNode : target){
    //     NodeID baseId = getBaseObjVar(tNode);
    //     if(baseId != tNode){
    //         GepObjVar* gep_o =  getGepObja(tNode);
    //         s32_t offset = gep_o->getLocationSet().getFldOff();
    //         std::cout << "not base object offset:"<< offset <<std::endl;

    //     }
    //     std::cout << "points-to***:"<< getPAG()->getGNode(tNode)->toString()   <<"\n";
    // }
    

    map<Type*, set<s32_t> >  type2Off;
    for(auto object: target){
        //NodeID baseId = getBaseObjVar(object);
        //and we should not use base here ?
        //we should not use base ,we can use type to filter out some object.

         std::cout << "object:"<< getPAG()->getGNode(object)->toString() <<"\n";

       
        s32_t offset = 0;
        NodeID baseId = getBaseObjVar(object);
        if(baseId != object){
            GepObjVar* gep_o =  getGepObja(object);
            offset = gep_o->getLocationSet().getFldOff();
            
        }
        std::cout << "offset:"<< offset <<"\n";
        llvm::Type* realType = nullptr;
        llvm::Type* DerType = nullptr;
        auto baseItr = ptrVir.find(baseId);  //here the baseId is error,due to that ptrVir's object is not base
                                             //so here the base is not meaning

        
        
        if (baseItr != ptrVir.end()){
           
           for(const auto& typeKey: baseItr->second){

                // std::string str0;
                // llvm::raw_string_ostream rso0(str0);
                // typeKey.first->print(rso0);
                // rso0.flush();
                // std::cout << "typeKey.first:"<< str0 << "\n";

                if(typeKey.second.find(vType) == typeKey.second.end())  //here ok,because it not baseId,but it did not get correct object type
                    continue;                                           //we should find all type here.

                //get all the type that are offset == offset object
                //here only for which case?
                //offset not equal vType offset.

                const auto & subStructkey = struct2subFld[typeKey.first];
                   
                auto iterReal = struct2subFld.end();
                for(const auto & tSubSubKey : subStructkey){
                    if(tSubSubKey.second.find(offset) != tSubSubKey.second.end()){
                        
                        if(!realType){
                            realType = tSubSubKey.first;
                            DerType = typeKey.first;
                            iterReal = struct2subFld.find(realType);
                        }else{
                            if(iterReal->second.find(tSubSubKey.first) == iterReal->second.end()){
                                
                                realType = tSubSubKey.first;
                                iterReal = struct2subFld.find(realType);
                                DerType = typeKey.first;
                            }
                        }
                    }
                }
                


             
            }

        }
            


        if(!DerType){
            auto IterObj = ptrVir.find(object);  //here the baseId is error,due to that ptrVir's object is not base
                                             //so here the base is not meaning
            if (IterObj == ptrVir.end())
                continue;

            for(const auto& typeKey: IterObj->second){


                if(typeKey.second.find(vType) == typeKey.second.end())  //here ok,because it not baseId,but it did not get correct object type
                    continue;                                           //we should find all type here.

                //get all the type that are offset == offset object
                //here only for which case?
                //offset not equal vType offset.

                const auto & subStructkey = struct2subFld[typeKey.first];
                   
                auto iterReal = struct2subFld.end();
                for(const auto & tSubSubKey : subStructkey){
                    if(tSubSubKey.second.find(offset) != tSubSubKey.second.end()){
                        
                        if(!realType){
                            realType = tSubSubKey.first;
                            DerType = typeKey.first;
                            iterReal = struct2subFld.find(realType);
                        }else{
                            if(iterReal->second.find(tSubSubKey.first) == iterReal->second.end()){
                                
                                realType = tSubSubKey.first;
                                iterReal = struct2subFld.find(realType);
                                DerType = typeKey.first;
                            }
                        }
                    }
                }


            }
        }

        if(DerType){
            type2Off[DerType].insert(offset);
            
           
        }else{
            std::cout<<"can not find real Type\n";
        }
        
        std::string str60;
        llvm::raw_string_ostream rso60(str60);
        realType->print(rso60);
        rso60.flush();
        std::cout << "realType:"<< str60 << "\n";

        
    }

    CallSite callSite = SVFUtil::getLLVMCallSite(cs->getCallSite());
    size_t idx = cppUtil::getVCallIdx(callSite);
    std::cout<<"idx:"<<idx <<"\n";
    
    std::vector<const SVFFunction*> destructorFun;
    //check the funName
    for(const auto& typeKey: type2Off){
        const SVFFunction* callee = nullptr;

        auto mainItr = vptr2Vt.find(typeKey.first);
        if(mainItr == vptr2Vt.end())
            continue;
        for(auto& tOff : typeKey.second){
            auto typeItr = mainItr->second.find(tOff);
            if (typeItr != mainItr->second.end() && typeItr->second.size() > idx) {
                callee = typeItr->second[idx];
                //show the callee name.
                std::cout<<"calleeName:"<<callee->getName()<<"\n";
                if(!callee)
                    std::cout << "can not find callee" << std::endl;
                else {
                    for(const auto& funKey: mainItr->second) {
                        if(funKey.second.size() <= idx)
                            continue;
                        destructorFun.push_back(funKey.second[idx]);
                    }
                }
            } else {
                std::cout << "can not find class with off" << std::endl;
            }

            //find the callee
            if(callee != nullptr){
                if (callSite.arg_size() == callee->arg_size() ||
                    (callSite.getFunctionType()->isVarArg() && callee->isVarArg()))
                {

                    // if argument types do not match
                    // skip this one
                    if (!checkArgTypesPointer(callSite, callee->getLLVMFun()))
                        continue;

                    cppUtil::DemangledName dname = cppUtil::demangle(callee->getName());
                    string calleeName = dname.funcName;

                    /*
                    * The compiler will add some special suffix (e.g.,
                    * "[abi:cxx11]") to the end of some virtual function:
                    * In dealII
                    * function: FE_Q<3>::get_name
                    * will be mangled as: _ZNK4FE_QILi3EE8get_nameB5cxx11Ev
                    * after demangling: FE_Q<3>::get_name[abi:cxx11]
                    * The special suffix ("[abi:cxx11]") needs to be removed
                    */
                    const std::string suffix("[abi:cxx11]");
                    size_t suffix_pos = calleeName.rfind(suffix);
                    if (suffix_pos != string::npos)
                        calleeName.erase(suffix_pos, suffix.size());

                    /*
                    * if we can't get the function name of a virtual callsite, all virtual
                    * functions calculated by idx will be valid
                    */
                    
                    if (calleeName[0] == '~')
                    {
                        for(auto fun:destructorFun){
                            vfns.insert(fun);
                            std::cout<<"insert2:"<<"\n";
                        }
                        // /virtualFunctions.insert(callee);
                    }else{
                        vfns.insert(callee);
                        std::cout<<"insert1:"<<"\n";
                    }

                    
                }
            }else{
                std::cout<< " callee is nullptr"<<std::endl;
            }
        }
        


    }

    connectVCallToVFns(cs, vfns, newEdges);
}






/*!
 * Find the alias check functions annotated in the C files
 * check whether the alias analysis results consistent with the alias check function itself
 */
void PointerAnalysis::validateSuccessTests(std::string fun)
{

    // check for must alias cases, whether our alias analysis produce the correct results
    if (const SVFFunction* checkFun = getFunction(fun))
    {
        if(!checkFun->getLLVMFun()->use_empty())
            outs() << "[" << this->PTAName() << "] Checking " << fun << "\n";

        for (Value::user_iterator i = checkFun->getLLVMFun()->user_begin(), e =
                    checkFun->getLLVMFun()->user_end(); i != e; ++i)
            if (SVFUtil::isCallSite(*i))
            {

                CallSite cs(*i);
                assert(cs.getNumArgOperands() == 2
                       && "arguments should be two pointers!!");
                Value* V1 = cs.getArgOperand(0);
                Value* V2 = cs.getArgOperand(1);
                AliasResult aliasRes = alias(V1, V2);

                bool checkSuccessful = false;
                if (fun == aliasTestMayAlias || fun == aliasTestMayAliasMangled)
                {
                    if (aliasRes == AliasResult::MayAlias || aliasRes == AliasResult::MustAlias)
                        checkSuccessful = true;
                }
                else if (fun == aliasTestNoAlias || fun == aliasTestNoAliasMangled)
                {
                    if (aliasRes == AliasResult::NoAlias)
                        checkSuccessful = true;
                }
                else if (fun == aliasTestMustAlias || fun == aliasTestMustAliasMangled)
                {
                    // change to must alias when our analysis support it
                    if (aliasRes == AliasResult::MayAlias || aliasRes == AliasResult::MustAlias)
                        checkSuccessful = true;
                }
                else if (fun == aliasTestPartialAlias || fun == aliasTestPartialAliasMangled)
                {
                    // change to partial alias when our analysis support it
                    if (aliasRes == AliasResult::MayAlias)
                        checkSuccessful = true;
                }
                else
                    assert(false && "not supported alias check!!");

                NodeID id1 = pag->getValueNode(V1);
                NodeID id2 = pag->getValueNode(V2);

                if (checkSuccessful)
                    outs() << sucMsg("\t SUCCESS :") << fun << " check <id:" << id1 << ", id:" << id2 << "> at ("
                           << getSourceLoc(*i) << ")\n";
                else
                {
                    SVFUtil::errs() << errMsg("\t FAILURE :") << fun
                                    << " check <id:" << id1 << ", id:" << id2
                                    << "> at (" << getSourceLoc(*i) << ")\n";
                    assert(false && "test case failed!");
                }
            }
            else
                assert(false && "alias check functions not only used at callsite??");

    }
}

/*!
 * Pointer analysis validator
 */
void PointerAnalysis::validateExpectedFailureTests(std::string fun)
{

    if (const SVFFunction* checkFun = getFunction(fun))
    {
        if(!checkFun->getLLVMFun()->use_empty())
            outs() << "[" << this->PTAName() << "] Checking " << fun << "\n";

        for (Value::user_iterator i = checkFun->getLLVMFun()->user_begin(), e =
                    checkFun->getLLVMFun()->user_end(); i != e; ++i)
            if (CallInst *call = SVFUtil::dyn_cast<CallInst>(*i))
            {
                assert(call->arg_size() == 2
                       && "arguments should be two pointers!!");
                Value* V1 = call->getArgOperand(0);
                Value* V2 = call->getArgOperand(1);
                AliasResult aliasRes = alias(V1, V2);

                bool expectedFailure = false;
                if (fun == aliasTestFailMayAlias || fun == aliasTestFailMayAliasMangled)
                {
                    // change to must alias when our analysis support it
                    if (aliasRes == AliasResult::NoAlias)
                        expectedFailure = true;
                }
                else if (fun == aliasTestFailNoAlias || fun == aliasTestFailNoAliasMangled)
                {
                    // change to partial alias when our analysis support it
                    if (aliasRes == AliasResult::MayAlias || aliasRes == AliasResult::PartialAlias || aliasRes == AliasResult::MustAlias)
                        expectedFailure = true;
                }
                else
                    assert(false && "not supported alias check!!");

                NodeID id1 = pag->getValueNode(V1);
                NodeID id2 = pag->getValueNode(V2);

                if (expectedFailure)
                    outs() << sucMsg("\t EXPECTED-FAILURE :") << fun << " check <id:" << id1 << ", id:" << id2 << "> at ("
                           << getSourceLoc(call) << ")\n";
                else
                {
                    SVFUtil::errs() << errMsg("\t UNEXPECTED FAILURE :") << fun << " check <id:" << id1 << ", id:" << id2 << "> at ("
                                    << getSourceLoc(call) << ")\n";
                    assert(false && "test case failed!");
                }
            }
            else
                assert(false && "alias check functions not only used at callsite??");
    }
}



void PointerAnalysis::getClassWithV()
{
    for (u32_t i = 0; i < LLVMModuleSet::getLLVMModuleSet()->getModuleNum(); ++i)
    {
        Module *M = LLVMModuleSet::getLLVMModuleSet()->getModule(i);
        
        for (Module::const_global_iterator I = M->global_begin(),
                E = M->global_end(); I != E; ++I)
        {
            const GlobalValue *globalvalue = SVFUtil::dyn_cast<const GlobalValue>(&(*I));

            if (isValVtbl(globalvalue) && globalvalue->getNumOperands() > 0)
            {
                string vtblClassName = getClassNameFromVtblObj(globalvalue);
                //std::cout << "111 error can not recSubFld" << "\n";
                classNameSet.insert(vtblClassName);       
            }
        }
    }


   
}


void PointerAnalysis::getClass2Name()
{
    for (u32_t i = 0; i < LLVMModuleSet::getLLVMModuleSet()->getModuleNum(); ++i)
    {
        Module *M = LLVMModuleSet::getLLVMModuleSet()->getModule(i);

         for (StructType *tStruct : M->getIdentifiedStructTypes()) {
            allStruct[M].insert(tStruct);
            if (tStruct->hasName()) {
                llvm::StringRef name = tStruct->getName();
                if (name.startswith("struct.")) {
                    name = name.drop_front(strlen("struct."));
                    string nameStr = name.str();
                    if(classNameSet.find(nameStr) != classNameSet.end()){
                        struct2NameMode[M][tStruct] = nameStr;
                        struct2Name[tStruct] = nameStr;
                        name2Struct[nameStr] = tStruct;
                    }
                    
                }else if(name.startswith("class.")){
                    name = name.drop_front(strlen("class."));
                    string nameStr = name.str();
                    if(classNameSet.find(nameStr) != classNameSet.end()){
                        struct2NameMode[M][tStruct] = nameStr;
                        struct2Name[tStruct] = nameStr;
                        name2Struct[nameStr] = tStruct;
                    }
                }else{
                    //llvm::outs() << "error:"<<name << "\n";
                }
            }
        }

    }


   
}



void PointerAnalysis::recSubFld(Type* targetType, Type* initType, s32_t accumulateOff){
    // Ensure that targetType is not a nullptr. If it is, then return.
    //std::cout << "zz3"<<  "\n";
    if(!targetType){
        std::cout << "error: targetType is nullptr" << "\n";
        return;
    }
    //std::cout << "hhhzz1"<<  "\n";
    auto iterFld = struct2Fld.find(targetType);
    if(iterFld == struct2Fld.end()){
        std::cout << "error: cannot find targetType in struct2Fld" << "\n";
        return;
    }
    //std::cout << "aaaazz1"<<  "\n";
    // Check if the size is less than or equal to 1.
    // == 1 means that the subType == type
    // if(iterFld->second.size() <= 1){
    //     return;
    // }
    //std::cout << "ggzz1"<<  "\n";
    // Recursive exploration.
    //std::cout << "class1-:"<< struct2Name[targetType]<< "   size:"<<  iterFld->second.size()<< "\n";
    //not filter out the type itself
    for(const auto & fldKey : iterFld->second){
        for(auto& t_off : fldKey.second){

            if(fldKey.first != targetType){
                recSubFld(fldKey.first, initType, accumulateOff + t_off);
            }
            struct2subFld[initType][fldKey.first].insert(accumulateOff + t_off);
            
        }
        
        
        
    }
    //std::cout << "wwwzz1"<<  "\n";
}


void PointerAnalysis::getClassFld()
{
    
    for (const auto& modeKey : struct2NameMode)
    {
        const llvm::DataLayout &DL = modeKey.first->getDataLayout();
        
        for (const auto& structKey : modeKey.second)
        {
            StructType* tSt = llvm::dyn_cast<llvm::StructType>(structKey.first);
            if (!tSt)
                continue;
            
            const llvm::StructLayout* SL = DL.getStructLayout(tSt);
            
            //bool isNestClass = false;
            for (unsigned i = 0, e = tSt->getNumElements(); i != e; ++i)
            {
                
                llvm::Type* elementType = tSt->getElementType(i)->isPointerTy() ? tSt->getElementType(i)->getPointerElementType() :  tSt->getElementType(i);
                
                if (elementType->isStructTy())
                {
                    // The element is a struct.
                    //here we do not care about the init type
                    // and we do not consider about sub-sub-sub class due to it never use dynamic_cast,
                    //so it meaning less.
                    //but what about 4 level class inheri?
                    // how should we do ?
                    
                    if (modeKey.second.find(elementType) != modeKey.second.end())
                    {
                        uint64_t offset = SL->getElementOffset(i);
                        struct2Fld[tSt][elementType].insert(offset);
                        //isNestClass = true;
                        //fld2Class[elementType].insert(tSt);
                        
                    }
                }
            }
            struct2Fld[tSt][tSt].insert(0);  //here should be that no matter which case the type itself should add to the set, not only about no child type
            //std::cout << "class:"<< structKey.second<< "   size:"<<  struct2Fld[tSt].size()<< "\n";

        }
    }
    
    for(auto& typeKey : struct2Fld){
        for(auto & subTypeKey : typeKey.second ){
            for(auto &t_off : subTypeKey.second){
                
                if(subTypeKey.first != typeKey.first){
                    recSubFld(subTypeKey.first,typeKey.first,t_off);
                }

                struct2subFld[typeKey.first][subTypeKey.first].insert(t_off);
 
            }
            
            
            //fld2Class[typeKey.first].emplace();
        }
    }

}









void PointerAnalysis::getAllCTOR()
{
    for (u32_t i = 0; i < LLVMModuleSet::getLLVMModuleSet()->getModuleNum(); ++i)
    {
        Module *M = LLVMModuleSet::getLLVMModuleSet()->getModule(i);

        for (llvm::Module::const_iterator iter = M->begin(), end = M->end(); iter != end; ++iter) {
            const llvm::Function *function = &*iter;
            // Print the name of each function
            if (function->arg_size() > 0){
                const llvm::Argument &firstArg = *(function->arg_begin());
                llvm::Type *argType = firstArg.getType()->isPointerTy() ? firstArg.getType()->getPointerElementType() : firstArg.getType();
                if(struct2Name.find(argType) != struct2Name.end()){
                    if(isConstructor(function)){  //this is error due to that we only care about class with virtual function,so here we need to make it
                        ctorSet.insert(function);
                        //std::cout << function->getName().str() << "\n";
                    }
                }
            }else{
                //this is error
            }
            

        }


        

    }


   
}






void PointerAnalysis::getVptr2Vt()
{
    auto* chGraph = SVFUtil::dyn_cast<CHGraph>(getCHGraph());

    for (const auto& typeKey : struct2Name)
    {
        const string& className = typeKey.second;
        Type* tSt = typeKey.first;

        CHNode* chNode = chGraph->getNode(className);
        if (!chNode){
            std::cout << "can not find CHNode class:"<< className << std::endl;
            continue;
        }
            

        auto iterFld = struct2subFld.find(tSt);  //we can not use struct2Fld
                                                 //so here we need to a set to get all the type's offset
                                                 //
        
        
        if (iterFld != struct2subFld.end())
        {
            set<s32_t> vtOff;
            for (const auto& subTypeKey : iterFld->second)   
            {
                for(const auto &offKey : subTypeKey.second){
                    vtOff.insert(offKey);
                }
            }

            size_t idx = 0;                                 //here is not that easy ,it is not that one subtype one vtable
                                                            //it is one loc one vtable
                                                            //
            for(const auto & tOff : vtOff){
                if (chNode->virtualFunctionVectors.size() <= idx)
                {
                    std::cout << "virtual fun size > idx" << std::endl;
                    continue;
                }
                vptr2Vt[tSt].insert({ tOff, chNode->virtualFunctionVectors[idx] });
                idx++;
            }
            
        }
        else  //this only for error handle
        {
            //this is error we do not forward handle
            //we just print error message
            //so here only for error handle 
            //struct2subFld include the type itself.
            std::cout << "getVptr2Vt can not find " << std::endl;
            // if (chNode->virtualFunctionVectors.size() > 1)
            // {
            //     std::cout << "virtual fun size > 1" << std::endl;
            // }
            // else if (!chNode->virtualFunctionVectors.empty())
            // {
            //     vptr2Vt[tSt].insert({ 0, chNode->virtualFunctionVectors[0] });
            // }
        }
    }
}




void PointerAnalysis::recSubFldOffForStruct(Type* targetType, Type* initType, s32_t accumulateOff){
    // Ensure that targetType is not a nullptr. If it is, then return.
    //std::cout << "zz3"<<  "\n";
    if(!targetType){
        std::cout << "error: targetType is nullptr" << "\n";
        return;
    }
    if(!targetType->isStructTy()){
        return;
    }
    //std::cout << "hhhzz1"<<  "\n";
    auto iterFld = allStruct2Fld.find(targetType);
    if(iterFld == allStruct2Fld.end()){
        std::cout << "error: cannot find targetType in allStruct2Fld" << "\n";
        return;
    }
    //std::cout << "aaaazz1"<<  "\n";
    // Check if the size is less than or equal to 1.
    // == 1 means that the subType == type
    // if(iterFld->second.size() <= 1){
    //     return;
    // }
    //std::cout << "ggzz1"<<  "\n";
    // Recursive exploration.
    //std::cout << "class1-:"<< struct2Name[targetType]<< "   size:"<<  iterFld->second.size()<< "\n";
    //not filter out the type itself
    for(const auto & fldKey : iterFld->second){
        for(auto & t_off : fldKey.second){
            if(fldKey.first != targetType){
                recSubFldOffForStruct(fldKey.first, initType, accumulateOff + t_off);
            }
            allStruct2FldOff[initType].insert(accumulateOff + t_off);      
        }

        
        
    }
    //std::cout << "wwwzz1"<<  "\n";
}

//array only contain same element
//strcut can contain different element
//so if it array, it only contain same element. no matter which element
//if struct contain array, it will be analysis in the element no matter how many level it contains and get it's finale element
//


void PointerAnalysis::getallStructFld()
{
    
    for (const auto& modeKey : allStruct)
    {
        const llvm::DataLayout &DL = modeKey.first->getDataLayout();
        
        for (const auto& structKey : modeKey.second)
        {
            StructType* tSt = llvm::dyn_cast<llvm::StructType>(structKey);
           
            if (!tSt)
                continue;
            if(!tSt->isSized()){
                continue;
            }
            if(allStruct2Fld.find(tSt) == allStruct2Fld.end()){
                
    
                s32_t sizeInBytes = DL.getTypeAllocSize(tSt);
                allStructAlig.emplace(tSt,sizeInBytes);
                
                const llvm::StructLayout* SL = DL.getStructLayout(tSt);
                if(SL == nullptr){
                    std::cout << "----gggssss---fffff-***********-"<< "\n";
                }
                
                
                //bool isNestClass = false;
                for (unsigned i = 0, e = tSt->getNumElements(); i != e; ++i)
                {
                    
                    //llvm::Type* elementType = tSt->getElementType(i);
                    llvm::Type* elementType = tSt->getElementType(i);
                    uint64_t offset = SL->getElementOffset(i);
                    
                    if(elementType->isArrayTy()){
                        
                        llvm::ArrayType* arrayType = llvm::dyn_cast<llvm::ArrayType>(elementType);
                        if(arrayType == nullptr){
                            std::cout << "arrayType == nullptr in getallStructFld"<< "\n";
                        }
                        getArrayVecEleRec(DL, arrayType , offset, structKey);
    
                    }else if(elementType->isVectorTy()){
                       
                        //llvm::VectorType* vecType = llvm::dyn_cast<llvm::VectorType>(elementType);
                        if(llvm::FixedVectorType* vecTypeFix = llvm::dyn_cast<llvm::FixedVectorType>(elementType)){  
                            if(vecTypeFix == nullptr){
                                std::cout << "vecTypeFix == nullptr in getallStructFld"<< "\n";
                            }
                            
                            getArrayVecEleRec(DL, vecTypeFix , offset, structKey);
                            
                        }
                        

                    }else{
                        
                        allStruct2Fld[tSt][elementType].insert(offset);
                    }
                    
                    
                    
                }
                allStruct2Fld[tSt][tSt].insert(0); 
                
            }
           
            
        }
    }
    
    for(auto& typeKey : allStruct2Fld){
        for(auto & subTypeKey : typeKey.second ){

            for(auto & t_off : subTypeKey.second){
                if(subTypeKey.first != typeKey.first){
                    recSubFldOffForStruct(subTypeKey.first,typeKey.first,t_off);
                }
                
                allStruct2FldOff[typeKey.first].insert(t_off);
            }


            //fld2Class[typeKey.first].emplace();
        }
    }


}

void PointerAnalysis::getArrayVecEleRec(const llvm::DataLayout &DL, llvm::Type * addType , uint64_t offset, llvm::Type * initType){
    
    if(!addType){
        return;
    }
    
    if (const llvm::ArrayType *arrayType = llvm::dyn_cast<llvm::ArrayType>(addType)) {
        
        llvm::Type *arrEleType = arrayType->getElementType();
        uint64_t elementSize = DL.getTypeAllocSize(arrEleType);
        int eleNum = arrayType->getArrayNumElements();
        
        for(int i= 0 ; i < eleNum;i++){
            allStruct2Fld[initType][arrEleType].insert(offset + i* elementSize);
            getArrayVecEleRec(DL, arrEleType, offset + i* elementSize, initType);
        }
        
        allStruct2Fld[initType][addType].insert(offset);
        
    }else if(const llvm::FixedVectorType *vecType = llvm::dyn_cast<llvm::FixedVectorType>(addType)){


        // std::string str0;
        // llvm::raw_string_ostream rso0(str0);
        // vecType->print(rso0);
        // rso0.flush();
        // std::cout << "type:"<< str0 << "\n";

        llvm::Type * vecEleType = vecType->getElementType();
        uint64_t elementSize = DL.getTypeAllocSize(vecEleType);
        int eleNum = vecType->getNumElements();

        for(int i= 0 ; i < eleNum;i++){
            allStruct2Fld[initType][vecEleType].insert(offset + i* elementSize);
            getArrayVecEleRec(DL, vecEleType, offset + i* elementSize, initType);
        }
        
        allStruct2Fld[initType][addType].insert(offset);
    }else{
        allStruct2Fld[initType][addType].insert(offset);
    }
    
}


void PointerAnalysis::addSubFldOff2all(const llvm::DataLayout &DL, llvm::Type * addType){
    if(!addType->isSized()){
        return;
    }
    if(addType->isVectorTy()){
        //llvm::VectorType* vecType = llvm::dyn_cast<llvm::VectorType>(addType);
        if(llvm::FixedVectorType* vecTypeFix = llvm::dyn_cast<llvm::FixedVectorType>(addType)){
            
            s32_t sizeInBytes = DL.getTypeAllocSize(addType);
            allStructAlig.emplace(addType,sizeInBytes);
            uint64_t offset = 0;
            if(vecTypeFix == nullptr){
                std::cout << "vecType == nullptr in getallStructFld"<< "\n";
            }
            getArrayVecEleRec(DL, vecTypeFix , offset, addType);
        }

    }else if(addType->isArrayTy()){
        s32_t sizeInBytes = DL.getTypeAllocSize(addType);
        allStructAlig.emplace(addType,sizeInBytes);

        uint64_t offset = 0;
        llvm::ArrayType* arrayType = llvm::dyn_cast<llvm::ArrayType>(addType);
        if(arrayType == nullptr){
            std::cout << "arrayType == nullptr in getArrGlobalValue"<< "\n";
        }
        getArrayVecEleRec(DL, arrayType, offset, addType);

    }else if(addType->isStructTy()){
        StructType* tSt = llvm::dyn_cast<llvm::StructType>(addType);
        if (!tSt){
            std::cout << "StructType == nullptr in getArrGlobalValue"<< "\n";
        }
        s32_t sizeInBytes = DL.getTypeAllocSize(addType);
        allStructAlig.emplace(addType,sizeInBytes);

        const llvm::StructLayout* SL = DL.getStructLayout(tSt);
        for (unsigned i = 0, e = tSt->getNumElements(); i != e; ++i)
        {
            //llvm::Type* elementType = tSt->getElementType(i);
            llvm::Type* elementType = tSt->getElementType(i);
            uint64_t offset = SL->getElementOffset(i);
            if(elementType->isArrayTy()){
                llvm::ArrayType* arrayType = llvm::dyn_cast<llvm::ArrayType>(elementType);
                if(arrayType == nullptr){
                    std::cout << "arrayType == nullptr in getallStructFld"<< "\n";
                }
                getArrayVecEleRec(DL, arrayType, offset, addType);
                
            }else if(elementType->isVectorTy()){
                //llvm::VectorType* vecType = llvm::dyn_cast<llvm::VectorType>(elementType);
                if(llvm::FixedVectorType* vecTypeFix = llvm::dyn_cast<llvm::FixedVectorType>(elementType)){
                    
                    //llvm::VectorType* vecType = llvm::dyn_cast<llvm::VectorType>(elementType);
                    if(vecTypeFix == nullptr){
                        std::cout << "vecType == nullptr in getallStructFld"<< "\n";
                    }
                    getArrayVecEleRec(DL, vecTypeFix, offset, addType);
                }

            }else{
                allStruct2Fld[tSt][elementType].insert(offset);
            }
            
            
        }
        allStruct2Fld[tSt][tSt].insert(0);  
    }
}


void PointerAnalysis::getArrType()
{
    int castCount = 0;
    int instCount = 0;
    std::set<const llvm::Value*> castInstSet;
    for (u32_t i = 0; i < LLVMModuleSet::getLLVMModuleSet()->getModuleNum(); ++i)
    {
        Module *M = LLVMModuleSet::getLLVMModuleSet()->getModule(i);
        const llvm::DataLayout &DL = M->getDataLayout();
        
        for (llvm::GlobalValue& GV : M->globals()){
            llvm::Type *gvType = GV.getType();
            if(allStruct2Fld.find(gvType) == allStruct2Fld.end()){
                addSubFldOff2all(DL, gvType);
            }
            
        }

        for (const auto &func : *M) {
            for (const auto &bb : func) {
                for (const auto &instr : bb) {
                    instCount++;
                    if (llvm::isa<llvm::CastInst>(instr)) {
                        // The operand is a cast instruction.
                        castInstSet.emplace(&instr);
                        castCount++;
                    }

                    llvm::Type * instType = instr.getType()->isPointerTy() ? instr.getType()->getPointerElementType() : instr.getType();
                    if(allStruct2Fld.find(instType) == allStruct2Fld.end()){
                        addSubFldOff2all(DL, instType);
                    }
                    
                    // Iterate through operands of the instruction.
                    for (const auto &op : instr.operands()) {
                        const llvm::Value* opVal = op.get();
                        llvm::Type * opValType = opVal->getType()->isPointerTy() ? opVal->getType()->getPointerElementType() : opVal->getType();
                        if(allStruct2Fld.find(opValType) == allStruct2Fld.end()){
                            addSubFldOff2all(DL, opValType);
                        }
                        if (llvm::isa<llvm::CastInst>(opVal)) {
                        // The operand is a cast instruction.
                            if(castInstSet.find(opVal) == castInstSet.end()){
                                // std::string str0;
                                // llvm::raw_string_ostream rso0(str0);
                                // opVal->print(rso0);
                                // rso0.flush();
                                // std::cout << "type:"<< str0 << "\n";
                                castCount++;
                            }
                            ;
                    }
                        
                        
                    }
                }
            }
        }


    }
    std::cout << "castinstCount:"<< castCount << "\n";
    std::cout << "instCount:"<< instCount << "\n";

}




void PointerAnalysis::printStructAndClass(){
    std::cout<<"------here struct2subFld\n";
    for(auto & typeKey: struct2subFld){
        std::cout<<"keyName:"<< struct2Name[typeKey.first]<<"\n";
        for(auto& subKey : typeKey.second){
            std::cout<<"subName:"<< struct2Name[subKey.first]<<"---";
            for(auto& tOff : subKey.second){
                std::cout<< tOff<<"---";
            }
            std::cout<<"\n";
        }
        std::cout<<"\n";
    } 
    std::cout<<"\n";
    std::cout<<"------------------------\n";
    // std::cout<<"------here allStruct2FldOff\n";
    // // for(auto& typeKey : allStruct2Fld ){
        
    // //     std::string str0;
    // //     llvm::raw_string_ostream rso0(str0);
    // //     typeKey.first->print(rso0);
    // //     rso0.flush();
    // //     //std::cout << "aaawww66inst:" <<str0 << std::endl;

    // //     std::cout<<"structName---:"<< str0<<"\n";
    // //     for(auto& eleKey : typeKey.second){
    // //         std::string str5;
    // //         llvm::raw_string_ostream rso5(str5);
    // //         eleKey.first->print(rso5);
    // //         rso5.flush();
    // //         //std::cout << "aaawww66:" <<str5 << std::endl;
    // //         std::cout<<"elementName:"<< str5 << "   off:" << eleKey.second <<"\n";
    // //     }
    // // }
    // for(auto & typeKey : allStruct2FldOff){
    //     std::string str0;
    //     llvm::raw_string_ostream rso0(str0);
    //     typeKey.first->print(rso0);
    //     rso0.flush();
    //     //std::cout << "aaawww66inst:" <<str0 << std::endl;
    //     std::cout<<"structName---:"<< str0<<"\n";
    //     for(auto &tOff : typeKey.second){
    //         std::cout<< "   off:" << tOff <<" ";
    //     }
    //     std::cout<< "\n";
    // }
}