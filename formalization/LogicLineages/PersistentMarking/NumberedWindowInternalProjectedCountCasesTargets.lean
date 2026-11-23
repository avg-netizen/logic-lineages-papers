module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountInductionTargets (project compared)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)

structure Inputs (r : Program 3) (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (rows pool outL outR removedL removedR full : OTerm α) : Prop where
  filteredLeft : D B Γ (filterGraph true outL rows pool)
  filteredRight : D B Γ (filterGraph false outR rows pool)
  acceptedLeft : D B Γ (loopAccept r outL removedL)
  acceptedRight : D B Γ (loopAccept r outR removedR)
  allProjected : D B Γ (project full rows)

def ExactOpenProjectedCountCases : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows pool outL outR removedL removedR full : OTerm α) (goal : Formula α),
    Inputs r B Γ rows pool outL outR removedL removedR full →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (pL pR joined : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (project pL (outL.relabel j)) →
      D B Δ (project pR (outR.relabel j)) →
      D B Δ (appendGraph joined pL pR) →
      D B Δ (compared (full.relabel j) joined) →
      D B Δ (goal.relabel j)) → D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesTargets
