module
public import LogicLineages.StandardControlCurrent.PolicyIndexedMergeProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedMerge.StatementChecks

theorem coordinatePartialRecursive : Partrec coordinate := coordinatePartrec

theorem mergePrefixPartialRecursive :
    Partrec (fun q : MergeArgs × Nat => prefixCode q.1 q.2) := prefixPartrec

theorem mergePartialRecursive : Partrec merge := mergePartrec

theorem coordinateExactForSuppliedIndex : ExactCoordinate := coordinateExact

theorem mergeExactForSuppliedIndex : ExactMerge := mergeExact

#print axioms coordinatePartialRecursive
#print axioms mergePrefixPartialRecursive
#print axioms mergePartialRecursive
#print axioms coordinateExactForSuppliedIndex
#print axioms mergeExactForSuppliedIndex
end LogicLineages.StandardControlCurrent.PolicyIndexedMerge.StatementChecks
