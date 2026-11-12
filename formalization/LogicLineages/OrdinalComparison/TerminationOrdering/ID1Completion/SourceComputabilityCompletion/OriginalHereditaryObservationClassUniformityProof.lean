module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationClassUniformityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationClassUniformityProof
open OriginalHereditaryObservationClassUniformityTargets

theorem sameKey : SameKey := by
  intro Q n arity symbols S c hS hQ Gamma q r hq hr he
  exact hQ Gamma q r hq hr
    ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hS Gamma q r hq hr).mp he)

theorem actualSameKey : ActualSameKey := by
  intro Q n arity data hd c ctx hc hS hQ Gamma q r hq hr he
  rw [OriginalRootObservationActualProof.representativeAtTyped n arity data hd c ctx hc Gamma q,
    OriginalRootObservationActualProof.representativeAtTyped n arity data hd c ctx hc Gamma r] at he
  exact sameKey Q n arity ctx.1.1 ctx.1.2 c hS hQ Gamma q r hq hr he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationClassUniformityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationClassUniformityProof
