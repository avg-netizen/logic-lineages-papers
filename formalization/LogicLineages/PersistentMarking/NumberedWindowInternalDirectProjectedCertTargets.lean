module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMemberTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectTargetMapOriginTargets (originRow)

def ExactProjectedCert : Prop :=
  ∀ (sourceObserver targetObserver : Program 2) (r : Program 3)
      (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (src dst kept removed inserted s t k d a p sk tp key : OTerm α) (goal : Formula α),
    Reports sourceObserver targetObserver r B Γ src dst kept removed inserted s t k d a p sk tp →
    Nonempty (Derivation B Γ (memberGraph p key)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (row dom cert : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (originRow (a.relabel j) (key.relabel j) row)) →
      NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Δ
        (removed.relabel j) row (d.relabel j) (key.relabel j) dom cert →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertTargets
