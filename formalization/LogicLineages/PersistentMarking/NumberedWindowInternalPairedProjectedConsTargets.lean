module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) : Prop :=
  Nonempty (Derivation B Γ f)

def ExactOpenPairedProjectedCons : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (left right row tailL tailR projL projR : OTerm α) (goal : Formula α),
    D B Γ (consGraph left row tailL) → D B Γ (consGraph right row tailR) →
    D B Γ (unary scratchTargets (suc projL) left) →
    D B Γ (unary scratchTargets (suc projR) right) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (target prevL prevR : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (unary scratchTargets (suc prevL) (tailL.relabel j)) →
      D B Δ (unary scratchTargets (suc prevR) (tailR.relabel j)) →
      D B Δ (consGraph (projL.relabel j) target prevL) →
      D B Δ (consGraph (projR.relabel j) target prevR) →
      D B Δ (goal.relabel j)) → D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsTargets
