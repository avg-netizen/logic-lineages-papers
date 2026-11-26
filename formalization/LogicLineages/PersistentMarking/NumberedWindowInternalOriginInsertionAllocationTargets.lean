module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionAllocationTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalOriginScanInductionTargets (Pools)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountInductionTargets (project compared)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)

structure Allocated (r : Program 3) (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (rows removed decoded rawL rawR scratchL scratchR joinedRemoved full
      outL outR pL pR joinedProjected : OTerm α) : Prop where
  removedPools : Pools B Γ removed decoded rawL rawR scratchL scratchR joinedRemoved
  filterL : D B Γ (filterGraph true outL rows scratchL)
  filterR : D B Γ (filterGraph false outR rows scratchL)
  loopL : D B Γ (loopAccept r outL rawL)
  loopR : D B Γ (loopAccept r outR rawR)
  projectL : D B Γ (project pL outL)
  projectR : D B Γ (project pR outR)
  orderedProjection : D B Γ (appendGraph joinedProjected pL pR)
  countProjection : D B Γ (compared full joinedProjected)

def ExactOpenOriginInsertionAllocation : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows removed decoded rawL rawR scratchL scratchR joinedRemoved full : OTerm α) (goal : Formula α),
    Pools B Γ removed decoded rawL rawR scratchL scratchR joinedRemoved →
    D B Γ (loopAccept r rows removed) →
    D B Γ (project full rows) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (outL outR pL pR joinedProjected : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Allocated r B Δ (rows.relabel j) (removed.relabel j) (decoded.relabel j)
        (rawL.relabel j) (rawR.relabel j) (scratchL.relabel j) (scratchR.relabel j)
        (joinedRemoved.relabel j) (full.relabel j) outL outR pL pR joinedProjected →
      D B Δ (goal.relabel j)) → D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionAllocationTargets
