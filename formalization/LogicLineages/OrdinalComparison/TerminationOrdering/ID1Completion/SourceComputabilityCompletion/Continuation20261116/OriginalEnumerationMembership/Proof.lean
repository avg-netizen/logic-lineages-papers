module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.FuelStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Induction InductionBindingProof

theorem internalMembership : Targets.InternalMembership := by
  intro n body alpha Delta node param p2 p3 out raw bound fuel types heads labels tupleBound hn hp h2 h3 he
  have hf : Nonempty (Derivation body Delta (AtFuel n fuel)) := fuelInduction n fuel (fun _ _ r ih => FuelStepProof.step n r ih)
  have hw := atFuelApply n fuel node param p2 p3 out raw bound types heads labels tupleBound hf
    (andIntro (andIntro (andIntro (andIntro hn hp) h2) h3) he)
  constructor
  · intro hm
    exact ⟨Derivation.implicationElimination (Classical.choice (andLeft hw)) (Classical.choice hm)⟩
  · intro hm
    exact ⟨Derivation.implicationElimination (Classical.choice (andRight hw)) (Classical.choice hm)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Proof
