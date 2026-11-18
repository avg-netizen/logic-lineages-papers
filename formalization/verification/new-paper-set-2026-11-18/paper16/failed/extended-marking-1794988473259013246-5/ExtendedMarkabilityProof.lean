import LogicLineages.PersistentMarking.ExtendedMarkingSupport
namespace LogicLineages.PersistentMarking.ExtendedMarkabilityProof
open Spine NameBridge ElementarySupportProof

theorem reflect (S : Signature) (s t r : Expr) (h : ExtendedWeakTree S s t) (hm : mark t = some r) :
    ∃ q, mark s = some q := by
  cases s with
  | free σ x => cases h; simp [mark] at hm
  | bound σ i => cases h
  | head f base => exact ⟨_,rfl⟩
  | marked f τ base extras => exact ⟨_,rfl⟩
  | lam σ body =>
    cases h with
    | @abs σ body τ tb x hp ht hf hg hc =>
      cases hb : mark tb with
      | none => simp [mark,hb] at hm
      | some tr =>
        have hop := markSubstitution (.cons (.free σ x) .nil) 0 tb tr hb
        obtain ⟨qr,hqr⟩ := reflect S (openBody σ x body) (openBody σ x tb) (openBody σ x tr) hc hop
        cases hs : mark body with
        | none =>
          have hh := RefinementMarkProof.markOpenMap σ x 0 body
          simp only [hs,Option.map_none] at hh
          rw [show mark (openBody σ x body) = none from hh] at hqr
          contradiction
        | some sr => exact ⟨.lam σ sr,by simp only [mark,hs,Option.map_some]⟩
termination_by nodes s
decreasing_by all_goals simp_all [nodes,openBody,openNodes] <;> omega

theorem reflectMarkability : ExtendedMarkingTargets.ReflectMarkability := by
  intro S s t r h hm
  obtain ⟨h⟩ := h
  exact reflect S s t r h hm
end LogicLineages.PersistentMarking.ExtendedMarkabilityProof
