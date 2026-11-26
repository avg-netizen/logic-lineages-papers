import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassEdge

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassWalkComplete
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowClassPathWitnessBits
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode

private theorem walk {S K Γ τ} (hk : DecisionSourceUniverse.Closed K)
    {x y : Class S K (finiteC Γ) τ} (h : RS S K (finiteC Γ) τ x y) :
    ∀ src dst, ActualCodeAt S K Γ τ src x → ActualCodeAt S K Γ τ dst y →
      ∃ es, es ≠ [] ∧ classWalkBit S K Γ τ src es dst = true := by
  induction h with
  | one he =>
    intro src dst hs hd
    obtain ⟨e,hb⟩ := NumberedWindowPathWitnessClassEdge.complete hk hs hd he
    refine ⟨[⟨dst,e⟩],by simp,?_⟩
    change (classEdgeBit S K Γ τ src dst e && decide (dst = dst)) = true
    simp [hb]
  | @more x y z he _ ih =>
    intro src dst hs hd
    obtain ⟨mid,hm⟩ := existsCode S K Γ τ hk y
    obtain ⟨e,hb⟩ := NumberedWindowPathWitnessClassEdge.complete hk hs hm he
    obtain ⟨es,_,hw⟩ := ih mid dst hm hd
    refine ⟨⟨mid,e⟩ :: es,by simp,?_⟩
    exact Bool.and_eq_true_iff.mpr ⟨hb,hw⟩

theorem complete {S K Γ τ src dst} {x y : Class S K (finiteC Γ) τ}
    (hk : DecisionSourceUniverse.Closed K)
    (hs : ActualCodeAt S K Γ τ src x) (hd : ActualCodeAt S K Γ τ dst y)
    (h : RS S K (finiteC Γ) τ x y) :
    ∃ es, positiveClassPathBit S K Γ τ src es dst = true := by
  obtain ⟨es,hne,hw⟩ := walk hk h src dst hs hd
  refine ⟨es,?_⟩
  simp only [positiveClassPathBit,Bool.and_eq_true,Bool.not_eq_true',
    List.isEmpty_eq_false_iff]
  exact ⟨hne,hw⟩

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassWalkComplete
