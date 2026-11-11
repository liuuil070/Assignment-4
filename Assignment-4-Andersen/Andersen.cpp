/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A4Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    using namespace SVF;
    ::WorkList<unsigned> workList;
    auto* pag = SVFIR::getPAG();
    pts.clear();

    auto propagate = [&](unsigned src, unsigned dst)
    {
        bool changed = false;
        for (unsigned object : pts[src])
            changed |= pts[dst].insert(object).second;
        if (changed)
            workList.push(dst);
    };
    auto addCopy = [&](unsigned src, unsigned dst)
    {
        for (unsigned id : {src, dst})
            if (!consg->hasConstraintNode(id))
                consg->addConstraintNode(new ConstraintNode(id), id);
        if (consg->addCopyCGEdge(src, dst))
            workList.push(src);  // A new edge must also propagate old points-to facts.
    };

    // Address constraints provide the initial points-to facts.
    for (const auto* edge : consg->getAddrCGEdges())
        if (pts[edge->getDstID()].insert(edge->getSrcID()).second)
            workList.push(edge->getDstID());

    set<pair<unsigned, unsigned>> resolvedCalls;
    do
    {
        while (!workList.empty())
        {
            unsigned pointer = workList.pop();
            const auto objects = pts[pointer];
            const auto* node = consg->getConstraintNode(pointer);

            // x = *p yields an object -> x copy constraint for every object in pts(p).
            for (const auto* edge : node->getLoadOutEdges())
                for (unsigned object : objects)
                    addCopy(object, edge->getDstID());

            // *p = x yields an x -> object copy constraint.
            for (const auto* edge : node->getStoreInEdges())
                for (unsigned object : objects)
                    addCopy(edge->getSrcID(), object);

            for (const auto* edge : node->getCopyOutEdges())
                propagate(pointer, edge->getDstID());

            for (const auto* edge : node->getGepOutEdges())
            {
                const auto* normal = SVFUtil::dyn_cast<NormalGepCGEdge>(edge);
                for (unsigned object : objects)
                {
                    set<unsigned> fields;
                    const auto* base = pag->getBaseObject(object);
                    if (consg->isBlkObjOrConstantObj(object) || base->isFieldInsensitive())
                        fields.insert(object);
                    else if (normal)
                    {
                        const auto& access = normal->getAccessPath();
                        // Include the leading pointer index (e.g. q + 1), not just struct indices.
                        const auto offset = access.isConstantOffset() ?
                                access.computeConstantOffset() : normal->getConstantFieldIdx();
                        fields.insert(consg->getGepObjVar(object, offset));
                    }
                    else
                    {
                        // Unknown indices conservatively include every field of the object.
                        fields.insert(base->getId());
                        for (unsigned offset = 0; offset < base->getMaxFieldOffsetLimit(); ++offset)
                            fields.insert(consg->getGepObjVar(base->getId(), offset));
                    }
                    for (unsigned field : fields)
                        if (pts[edge->getDstID()].insert(field).second)
                            workList.push(edge->getDstID());
                }
            }
        }

        // New function-pointer targets introduce actual/formal and return constraints.
        for (const auto& call : consg->getIndirectCallsites())
        {
            const auto* site = call.first;
            const auto targets = pts[call.second];
            for (unsigned target : targets)
            {
                if (!consg->isFunction(target))
                    continue;
                const auto* function = consg->getFunction(target);
                if (!SVFUtil::matchArgs(site, function) ||
                        !resolvedCalls.insert({site->getId(), function->getId()}).second)
                    continue;

                if (pag->hasCallSiteArgsMap(site) && pag->hasFunArgsList(function))
                {
                    const auto& actuals = pag->getCallSiteArgsList(site);
                    const auto& formals = pag->getFunArgsList(function);
                    auto actual = actuals.begin();
                    auto formal = formals.begin();
                    for (; actual != actuals.end() && formal != formals.end(); ++actual, ++formal)
                        if ((*actual)->isPointer() && (*formal)->isPointer())
                            addCopy((*actual)->getId(), (*formal)->getId());
                    if (function->isVarArg())
                        for (; actual != actuals.end(); ++actual)
                            if ((*actual)->isPointer())
                                addCopy((*actual)->getId(), pag->getVarargNode(function));
                }
                const auto* returnSite = site->getRetICFGNode();
                if (pag->funHasRet(function) && pag->callsiteHasRet(returnSite))
                {
                    const auto* returned = pag->getFunRet(function);
                    const auto* received = pag->getCallSiteRet(returnSite);
                    if (returned->isPointer() && received->isPointer())
                        addCopy(returned->getId(), received->getId());
                }
            }
        }
    } while (!workList.empty());
}
