module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionTargets
public import LogicLineages.OrdinalComparison.SignedShiftCollectionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection.StatementChecks
theorem original_domain_and_rebasing : Targets.OriginalDomainAndRebasing :=
  Proof.originalDomainAndRebasing
theorem exact_collection_and_support : Targets.ExactCollectionAndSupport :=
  Proof.exactCollectionAndSupport
theorem actual_greatest_surviving_shift : Targets.ActualGreatestSurvivingShift :=
  Proof.actualGreatestSurvivingShift
theorem uniform_primitive_recursive_data : Targets.UniformPrimitiveRecursiveData :=
  Proof.uniformPrimitiveRecursiveData
end LogicLineages.OrdinalComparison.SignedShiftCollection.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SignedShiftCollection
