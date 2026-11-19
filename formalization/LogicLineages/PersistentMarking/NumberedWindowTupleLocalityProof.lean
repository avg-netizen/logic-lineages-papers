import LogicLineages.PersistentMarking.NumberedWindowFullLocalityTargets
import LogicLineages.PersistentMarking.NumberedWindowTupleSplitChecks
import LogicLineages.PersistentMarking.NumberedWindowApplicationPathProof

namespace LogicLineages.PersistentMarking.NumberedWindowTupleLocalityProof
open NumberedWindowDomain NumberedWindowPathLocality NumberedWindowFullLocalityTargets

theorem visit {S K C τ q r u} {p : NumberedWindowRules.WindowPath S K C τ q r}
    (h : Visits S K C τ p u) : InWindow S K C τ u := by
  induction h with
  | start path => exact (NumberedWindowApplicationPathProof.endpoints path).1
  | next _ _ _ ih => exact ih

theorem constructed : ConstructedTupleLocality := by
  intro S K Γ q r args σ τ n Q As
  dsimp only
  intro hK hq hValid hArgs hArgsValid hQ hAs hEq hReal hReals
  obtain ⟨start,out,hApp,path,hOut⟩ :=
    NumberedWindowTupleSplitChecks.exact_WholeTupleSimulation S K Γ q r args σ τ n Q As
      hK hq hValid hArgs hArgsValid hQ hAs hEq hReal hReals
  exact ⟨start,out,hApp,path,fun _ hHere => visit hHere,hOut⟩

end LogicLineages.PersistentMarking.NumberedWindowTupleLocalityProof
