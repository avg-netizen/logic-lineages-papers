import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceRoots
import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermLift
import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceBaseLift
import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceConsLift

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceComplete
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimarySequence NumberedWindowPrimarySequenceRoots
open NumberedWindowPrimarySequenceTermTrace NumberedWindowPrimarySequenceTermLift
open NumberedWindowPrimarySequenceBaseLift NumberedWindowPrimarySequenceConsLift

theorem term {S K C τ Q R} (h : Primary S K C τ Q R) :
    Nonempty (TypedExchangeTrace S K C τ Q R) := by
  induction h using Primary.rec
    (motive_2 := fun C types qs rs _ => Nonempty (TypedArgsExchangeTrace S K C types qs rs)) with
  | refl ht => exact ⟨.refl ht⟩
  | symm _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨termReverse p⟩
  | trans _ _ iq ir =>
    obtain ⟨p⟩ := iq
    obtain ⟨q⟩ := ir
    exact ⟨termAppend p q⟩
  | ordinary hf hg he e hb hc hp => exact ⟨ordinaryRoot hf hg he e hb hc hp⟩
  | numbered hf hg he hb hc hx hp => exact ⟨numberedRoot hf hg he hb hc hx hp⟩
  | lam _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨underLam p⟩
  | appFunction _ ha ih =>
    obtain ⟨p⟩ := ih
    exact ⟨inFunction p ha⟩
  | appArgument hq _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨inArgument hq p⟩
  | ordinaryArguments _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨underOrdinary p⟩
  | numberedBase _ hx ih =>
    obtain ⟨p⟩ := ih
    exact ⟨underNumberedBase p hx⟩
  | numberedExtras hb _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨underNumberedExtras hb p⟩
  | nil => exact ⟨.refl .nil⟩
  | cons _ _ iq ia => exact consNonempty iq ia

private theorem argsFixed (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (qs rs : NArgs) (types : List Ty) (h : OrderedPrimary S K C types qs rs) :
    Nonempty (TypedArgsExchangeTrace S K C types qs rs) := by
  cases qs with
  | nil => cases h; exact ⟨.refl .nil⟩
  | cons Q qs =>
    cases h with
    | cons hq ht => exact consNonempty (term hq) (argsFixed S K C qs _ _ ht)
termination_by structural qs

theorem args {S K C types qs rs} (h : OrderedPrimary S K C types qs rs) :
    Nonempty (TypedArgsExchangeTrace S K C types qs rs) := argsFixed S K C qs rs types h

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceComplete
