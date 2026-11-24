module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

def ExactOpenTargetMapCons : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (code row tail projected : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (consGraph code row tail)) →
    Nonempty (Derivation B Γ (unary scratchTargets (suc projected) code)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (headTarget tailTargets : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (unary (guardAt 4) (suc z) (row.relabel j))) →
      Nonempty (Derivation B Δ (unary (field 0) headTarget (row.relabel j))) →
      Nonempty (Derivation B Δ (unary scratchTargets (suc tailTargets) (tail.relabel j))) →
      Nonempty (Derivation B Δ (consGraph (projected.relabel j) headTarget tailTargets)) →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsTargets
