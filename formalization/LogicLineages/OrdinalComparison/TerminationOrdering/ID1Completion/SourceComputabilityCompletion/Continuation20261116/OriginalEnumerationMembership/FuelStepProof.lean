module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.FuelStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open Induction InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph AtFuel

theorem step (n : Nat) (fuel : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowFuel n fuel))) :
    Nonempty (Derivation body Delta (AtFuel n fuel)) := by
  apply zeroSuccessorCases Delta fuel _
  · have hz : Nonempty (Derivation body (eqn fuel z :: Delta) (eqn fuel z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact InductionTransportProof.atTransport n z fuel ⟨symm (Classical.choice hz)⟩ (ZeroInductionProof.atZero n)
  · intro beta j Theta pred hj hf
    rw [atFuelRename]
    have ihj := renameInto ih j Theta hj
    rw [belowFuelRename] at ihj
    have hs := PositiveInductionProof.atSuccessor n pred
      (InductionTransportProof.belowTransport n (fuel.relabel j) (suc pred) hf ihj)
    exact InductionTransportProof.atTransport n (suc pred) (fuel.relabel j) ⟨symm (Classical.choice hf)⟩ hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.FuelStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.FuelStepProof
