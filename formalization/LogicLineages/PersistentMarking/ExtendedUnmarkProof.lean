import LogicLineages.PersistentMarking.ExtendedMarkingSupport
namespace LogicLineages.PersistentMarking.ExtendedUnmarkProof
open Spine NameBridge ElementarySupportProof ExtendedMarkingSupport

theorem remove (S : Signature) (s t : Expr) (h : ExtendedWeakTree S (headmark s) t) : ExtendedWeak S s t := by
  cases s with
  | free σ x => exact ⟨h⟩
  | bound σ i => exact ⟨h⟩
  | marked f τ base extras => exact ⟨h⟩
  | head f base =>
    have hf := ExtendedEndpointProof.weakFacts h
    have hp : PaperTerm S (.head f base) f.result := paperBack S _ _ hf.1
    have he : t.type = f.result := hf.2.2.symm
    have ht : PaperTerm S t f.result := he ▸ hf.2.1
    exact ⟨.put hp ht h⟩
  | lam σ body =>
    cases h with
    | @abs σ mb τ tb x hp ht hfb hft hc =>
      have hbody : ExtendedWeakTree S (headmark (openBody σ x body)) (openBody σ x tb) := by
        simpa only [openBody,opening] using hc
      obtain ⟨hc'⟩ := remove S (openBody σ x body) (openBody σ x tb) hbody
      have hs : PaperTerm S (.lam σ body) (.arrow σ τ) := paperBack S _ _ hp
      have hf : freeOccurs (σ,x) body = false := (names (σ,x) body).symm.trans hfb
      exact ⟨.abs hs ht hf hft hc'⟩
termination_by nodes s
decreasing_by all_goals simp_all [nodes,openBody,openNodes] <;> omega

theorem removeSource : ExtendedMarkingTargets.RemoveSource := by
  intro S s t h
  obtain ⟨h⟩ := h
  exact remove S s t h
end LogicLineages.PersistentMarking.ExtendedUnmarkProof
