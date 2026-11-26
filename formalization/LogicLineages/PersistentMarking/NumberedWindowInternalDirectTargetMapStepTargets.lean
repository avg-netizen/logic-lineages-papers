module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStepTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (targetStep joined)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

/-- Opening precisely the chosen guarded step. Zero tail cannot give a
successful result. The report retains the prior result at its actual
successor and the real selected cons-building call on the same input pair. -/
def ExactOpenTargetMapStep : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (row previous projected : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph targetStep (suc projected) ![row,previous])) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (tail : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (eqn (previous.relabel j) (suc tail))) →
      Nonempty (Derivation B Δ (unary (guardAt 4) (suc z) (row.relabel j))) →
      Nonempty (Derivation B Δ (programGraph joined (projected.relabel j)
        ![row.relabel j,previous.relabel j])) →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStepTargets
