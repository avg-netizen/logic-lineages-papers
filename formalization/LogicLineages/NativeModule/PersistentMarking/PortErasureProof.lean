module

public import LogicLineages.NativeModule.PersistentMarking.PortNormalizationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.PortErasureProof
open Spine NameBridge DecisionPorts

theorem weak (S K V Γ q t) (h : PortComparison.Weak S K V Γ q t) : Spine.Weak S q t := by
  refine PortComparison.Weak.rec
    (motive_1 := fun _ q t _ => Spine.Weak S q t)
    (motive_2 := fun _ q t _ => Spine.Strict S q t)
    (motive_3 := fun _ qs ts _ => Spine.Matching S qs ts)
    (motive_4 := fun _ qs ts _ => Spine.Multiset S qs ts)
    (motive_5 := fun _ qs ts _ => Spine.Coverage S qs ts)
    (motive_6 := fun _ f bs es ts _ => Spine.Whole S f bs es ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; exact .var
  · intros; rename_i hs ht hK hi hx hy child ih; exact .abs hs ht hx hy ih
  · intros; rename_i hs ht heq hty child ih; exact .funHead hs ht heq hty ih
  · intros; rename_i hs ht child ih; exact .put hs ht ih
  · intros; rename_i hs ht hat hty happ child ih; exact .select hs ht hat hty happ ih
  · intros; rename_i hs ht hK hi hx hy child ih; exact .fabs hs ht hx hy ih
  · intros; rename_i hs ht hp child ih; exact .copy hs ht hp ih
  · intros; rename_i hs ht heq hm hw ihm ihw; exact .stat hs ht heq ihm ihw
  · intros; rename_i hs ht hmark child ih; exact .intro hs ht hmark ih
  · intros; exact .nil
  · intros; rename_i hr hw hm ihw ihm; exact .cons hr ihw ihm
  · intros; rename_i hs ht hn hm hc ihm ihc; exact .replace hs ht hn ihm ihc
  · intros; exact .nil
  · intros; rename_i hat hs hc ihs ihc; exact .cons hat ihs ihc
  · intros; exact .nil
  · intros; rename_i hw hs ihw ihs; exact .cons ihw ihs

theorem strict (S K V Γ q t) (h : PortComparison.Strict S K V Γ q t) : Spine.Strict S q t := by
  cases h with | intro hs ht hm hw => exact .intro hs ht hm (weak S K V Γ _ _ hw)
theorem matching (S K V Γ qs ts) (h : PortComparison.Matching S K V Γ qs ts) : Spine.Matching S qs ts := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs => cases h with
    | cons hr hw hm => exact .cons hr (weak _ _ _ _ _ _ hw) (matching _ _ _ _ _ _ hm)
termination_by sizeOf qs
theorem coverage (S K V Γ qs ts) (h : PortComparison.Coverage S K V Γ qs ts) : Spine.Coverage S qs ts := by
  cases ts with
  | nil => cases h; exact .nil
  | cons t ts => cases h with
    | cons hat hs hc => exact .cons hat (strict _ _ _ _ _ _ hs) (coverage _ _ _ _ _ _ hc)
termination_by sizeOf ts
theorem multiset (S K V Γ qs ts) (h : PortComparison.Multiset S K V Γ qs ts) : Spine.Multiset S qs ts := by
  cases h with
  | replace hs ht hn hm hc => exact .replace hs ht hn (matching _ _ _ _ _ _ hm) (coverage _ _ _ _ _ _ hc)
theorem whole (S K V Γ f bs es ts) (h : PortComparison.Whole S K V Γ f bs es ts) : Spine.Whole S f bs es ts := by
  cases ts with
  | nil => cases h; exact .nil
  | cons t ts => cases h with
    | cons hw hs => exact .cons (weak _ _ _ _ _ _ hw) (whole _ _ _ _ _ _ _ _ hs)
termination_by sizeOf ts

theorem erasure : PortNormalizationTargets.Erasure := ⟨weak,strict,matching,multiset,coverage,whole⟩
end LogicLineages.PersistentMarking.PortErasureProof
