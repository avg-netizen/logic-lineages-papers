module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedUnmarkProof
public import LogicLineages.NativeModule.PersistentMarking.ExtendedMarkabilityProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedMarkingProof
open Spine NameBridge ExtendedMarkingSupport

def Result (S : Signature) : ExtendedJudgment → Prop
  | .weak s t => ExtendedWeak S (headmark s) (headmark t)
  | _ => True

theorem transport (S : Signature) (j : ExtendedJudgment) (h : ExtendedTree S j) : Result S j := by
  induction h with
  | var => exact ⟨.var⟩
  | @abs σ s τ t x hp ht hfs hft hc ih =>
    obtain ⟨hi⟩ := ih
    have hbody : ExtendedWeakTree S (openBody σ x (headmark s)) (openBody σ x (headmark t)) := by
      simpa only [openBody,opening] using hi
    exact ⟨.abs (paperForward S _ _ hp) (paperForward S _ _ ht)
      ((names (σ,x) s).trans hfs) ((names (σ,x) t).trans hft) hbody⟩
  | @funHead f ss g ts hp ht heq he hm ih =>
    have hpf := paperForward S _ _ hp
    have hpt := paperForward S _ _ ht
    have hew : ExtendedWeak S (.marked f g.result ss .nil) (.marked g g.result ts .nil) :=
      ⟨.inHead (he ▸ hpf) hpt heq hm .orderedNil⟩
    simpa only [Result,headmark,he] using hew
  | put hp ht hc ih => exact ih
  | @select f τ ss es t i q domains r hp ht ha hq hcall hc ih =>
    obtain ⟨hr⟩ := ExtendedUnmarkProof.removeSource S r (headmark t) ih
    exact ⟨.select hp (paperForward S _ _ ht) ha hq hcall hr⟩
  | @fabs f σ τ ss es body x hp ht hf hg hc ih =>
    obtain ⟨hi⟩ := ih
    have hbody : ExtendedWeakTree S (.marked f τ ss (es.append (.cons (.free σ x) .nil)))
        (openBody σ x (headmark body)) := by
      simpa only [headmark,openBody,opening] using hi
    exact ⟨.fabs hp (paperForward S _ _ ht) hf ((names (σ,x) body).trans hg) hbody⟩
  | copy hp ht hpref hc ih =>
    exact ⟨.marked1 hp (paperForward S _ _ ht) hpref hc .wholeNil⟩
  | stat hp ht heq hm hw ihm ihw =>
    exact ⟨.marked2 hp (paperForward S _ _ ht) heq hm hw .wholeNil⟩
  | inHead hp ht heq hm ho ihm iho => exact ⟨.inHead hp ht heq hm ho⟩
  | marked1 hp ht hpref hb he ihb ihe => exact ⟨.marked1 hp ht hpref hb he⟩
  | marked2 hp ht heq hm hb he ihm ihb ihe => exact ⟨.marked2 hp ht heq hm hb he⟩
  | drop hp ht hc ih =>
    obtain ⟨hi⟩ := ih
    exact ⟨.drop hp (paperForward S _ _ ht) hi⟩
  | perm hp ht hperm hc ih =>
    obtain ⟨hi⟩ := ih
    exact ⟨.perm hp (paperForward S _ _ ht) hperm hi⟩
  | copies hp ht hcopies hc ih =>
    obtain ⟨hi⟩ := ih
    exact ⟨.copies hp (paperForward S _ _ ht) hcopies hi⟩
  | @pselect f τ base extras t i q domains args r hp ht ha hq htuple hcall hc ih =>
    obtain ⟨hr⟩ := ExtendedUnmarkProof.removeSource S r (headmark t) ih
    exact ⟨.pselect hp (paperForward S _ _ ht) ha hq htuple hcall hr⟩
  | strictIntro _ _ _ _ _ => trivial
  | matchingNil => trivial
  | matchingCons _ _ _ _ _ => trivial
  | multisetReplace _ _ _ _ _ _ _ => trivial
  | coverageNil => trivial
  | coverageCons _ _ _ _ _ => trivial
  | wholeNil => trivial
  | wholeCons _ _ _ _ => trivial
  | orderedNil => trivial
  | orderedCons _ _ _ _ => trivial

theorem forward : ExtendedMarkingTargets.Forward := by
  intro S s t h
  obtain ⟨h⟩ := h
  exact transport S _ h

theorem fullMarking : ExtendedMarkingTargets.FullMarking :=
  ⟨forward,ExtendedUnmarkProof.removeSource,ExtendedMarkabilityProof.reflectMarkability⟩
end LogicLineages.PersistentMarking.ExtendedMarkingProof
