module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalApplicationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalApplicationPathProof
open NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowExternalApplicationTargets

theorem literal : QuotientApplicationLiteral := by
  intro S K C σ τ hk q u
  exact ⟨rfl, rfl⟩

private theorem liftEdge {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    (u : Class S K C σ) {q r : Class S K C (.arrow σ τ)}
    (edge : ClassEdge q r) : ClassEdge (appClass hk q u) (appClass hk r u) := by
  refine Quot.inductionOn u ?_
  intro arg
  obtain ⟨before, after, rfl, rfl, step⟩ := edge
  exact ⟨appCarrier hk before arg, appCarrier hk after arg, rfl, rfl, .auxFunction step⟩

/-- Transport each positive class edge under a fixed argument by the
actual raw function-side rule. The nonempty path uses the same edge count. -/
theorem positive : QuotientAppPreservesPositive := by
  intro S K C σ τ hk q r u path
  induction path with
  | one edge => exact .one (liftEdge hk u edge)
  | more edge _ ih => exact .more (liftEdge hk u edge) ih

end LogicLineages.PersistentMarking.NumberedWindowExternalApplicationPathProof
