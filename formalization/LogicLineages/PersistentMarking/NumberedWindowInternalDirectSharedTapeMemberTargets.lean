module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMemberTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Given actual scratch membership on the shared inserted tape, the accepted
physical row's parser and dominator report are on the very same removed scratch
payload as the source partition. No synthetic membership is introduced. -/
def ExactOpenSharedTapeMember : Prop :=
  ∀ (sourceObserver targetObserver : Program 2) (r : Program 3)
      (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (src dst kept removed inserted s t k d a p sk tp row : OTerm α) (goal : Formula α),
    Reports sourceObserver targetObserver r B Γ src dst kept removed inserted s t k d a p sk tp →
    Nonempty (Derivation B Γ (memberGraph a row)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (target dom cert : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Δ (removed.relabel j) (row.relabel j) (d.relabel j) target dom cert →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMemberTargets
