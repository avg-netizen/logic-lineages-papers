module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingStatementChecks

theorem fixedTypeClosure : FullTuplePackingTargets.TypeClosure := FullTuplePackingProof.typeClosure
theorem fixedExactLength : FullTuplePackingTargets.ExactLength := FullTuplePackingProof.exactLength
theorem fixedExactEntry : FullTuplePackingTargets.ExactEntry := FullTuplePackingProof.exactEntry
theorem fixedMembership : FullTuplePackingTargets.Membership := FullTuplePackingProof.membership
theorem fixedPointwiseDomination : FullTuplePackingTargets.PointwiseDomination := FullTuplePackingProof.pointwiseDomination
theorem fixedWeakeningMap : FullTuplePackingTargets.WeakeningMap := FullTuplePackingProof.weakeningMap

#print axioms fixedTypeClosure
#print axioms fixedExactLength
#print axioms fixedExactEntry
#print axioms fixedMembership
#print axioms fixedPointwiseDomination
#print axioms fixedWeakeningMap
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering
end LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingStatementChecks
