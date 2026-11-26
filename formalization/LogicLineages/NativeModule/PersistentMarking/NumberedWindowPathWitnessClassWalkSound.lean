module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPathWitnessClassEdge

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassWalkSound
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowClassPathWitnessBits
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode

private theorem walk {S K Γ τ} (hk : DecisionSourceUniverse.Closed K) :
    ∀ es src dst, es ≠ [] → classWalkBit S K Γ τ src es dst = true →
      ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧
        RS S K (finiteC Γ) τ x y := by
  intro es
  induction es with
  | nil =>
    intro src dst hne _
    exact False.elim (hne rfl)
  | cons e rest ih =>
    intro src dst _ h
    change (classEdgeBit S K Γ τ src e.targetCode e.edge &&
      classWalkBit S K Γ τ e.targetCode rest dst) = true at h
    obtain ⟨he,hrest⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨x,y,hx,hy,hxy⟩ := NumberedWindowPathWitnessClassEdge.sound he
    cases rest with
    | nil =>
      change decide (e.targetCode = dst) = true at hrest
      have ec : e.targetCode = dst := of_decide_eq_true hrest
      rw [ec] at hy
      exact ⟨x,y,hx,hy,.one hxy⟩
    | cons f fs =>
      obtain ⟨y',z,hy',hz,hyz⟩ := ih _ _ (by simp) hrest
      have eyy : y = y' := sameClass hk hy hy'
      rw [eyy] at hxy
      exact ⟨x,z,hx,hz,.more hxy hyz⟩

theorem sound {S K Γ τ src dst es} (hk : DecisionSourceUniverse.Closed K)
    (h : positiveClassPathBit S K Γ τ src es dst = true) :
    ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧
      RS S K (finiteC Γ) τ x y := by
  simp only [positiveClassPathBit,Bool.and_eq_true,Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  exact walk hk es src dst h.1 h.2

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassWalkSound
