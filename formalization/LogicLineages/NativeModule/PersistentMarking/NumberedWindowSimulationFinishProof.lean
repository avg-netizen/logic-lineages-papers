module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationFoldProof
public import LogicLineages.NativeModule.PersistentMarking.LiteralWindowLocalityProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationFinishProof
open LiteralDerivationTree LiteralDerivationLocalityTargets
open NumberedWindowDomain NumberedWindowSimulationJobs NumberedWindowPositiveSimulationTargets

private theorem foot {S K J} (d : Tree S J) (hk : DecisionSourceUniverse.Closed K)
    (hRoots : ∀ τ, τ ∈ rootTypes J → τ ∈ K) : Foot K d :=
  LiteralWindowLocalityProof.locality S K J d hk hRoots

theorem weak : BudgetedWeakSimulation := by
  intro S K q t d hk hq ht n Q hb hQ
  have hFoot := foot d hk (fun τ h => (List.mem_append.mp h).elim (hq τ) (ht τ))
  exact NumberedWindowSimulationFoldProof.all S K hk d hFoot n Q hb hQ

theorem strict : BudgetedStrictSimulation := by
  intro S K q t d hk hq ht n Q hb hQ
  have hFoot := foot d hk (fun τ h => (List.mem_append.mp h).elim (hq τ) (ht τ))
  exact NumberedWindowSimulationTraceProof.strictly
    (NumberedWindowSimulationFoldProof.all S K hk d hFoot n Q hb hQ)

end LogicLineages.PersistentMarking.NumberedWindowSimulationFinishProof
