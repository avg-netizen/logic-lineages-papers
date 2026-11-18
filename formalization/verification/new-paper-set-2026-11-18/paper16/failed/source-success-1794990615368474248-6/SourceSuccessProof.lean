import LogicLineages.PersistentMarking.OriginalCallShape
namespace LogicLineages.PersistentMarking.SourceSuccessProof
open Spine NameBridge ElementarySupportProof OriginalCallShape

theorem blockedTransport (S : Signature) (q s : Expr) (h : ExtendedWeakTree S q s) (n : Nat)
    (hb : Blocked q n) : Blocked s n := by
  cases n with
  | zero => exact False.elim hb
  | succ n =>
    cases q with
    | free σ x => cases h; exact hb
    | bound σ i => cases h
    | head f base => exact False.elim hb
    | marked f τ base extras => exact False.elim hb
    | lam σ body =>
      cases h with
      | @abs σ body τ target x hp ht hx hy hc =>
        have hbo : Blocked (openBody σ x body) n := (OriginalCallShape.opening σ x 0 body n).mpr hb
        have hto := blockedTransport S (openBody σ x body) (openBody σ x target) hc n hbo
        exact (OriginalCallShape.opening σ x 0 target n).mp hto
termination_by nodes q
decreasing_by all_goals simp_all [openBody,nodes,openNodes] <;> omega

theorem orderedLength {S : Signature} {as bs : Args} (h : ExtendedOrderedTree S as bs) : as.length = bs.length := by
  cases as with
  | nil => cases h; rfl
  | cons a rest =>
    cases h with
    | orderedCons ha hr =>
      have hi := orderedLength hr
      simp only [Args.length,hi]
termination_by sizeOf as

theorem sourceSuccess : ApplicationCovarianceTargets.SourceSuccess := by
  intro S q s as bs τ r he hab hqa hsb hs
  obtain ⟨he⟩ := he
  obtain ⟨hab⟩ := hab
  have hlen := orderedLength hab
  have hnot := (fullSuccess s bs τ hsb).mp ⟨r,hs⟩
  apply (fullSuccess q as τ hqa).mpr
  intro hblock
  have hb := blockedTransport S q s he as.length hblock
  exact hnot (hlen ▸ hb)
end LogicLineages.PersistentMarking.SourceSuccessProof
