module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedMultisetNormalizationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedMultisetNormalizationProof
open Source RankedTree RankedPathOrder

theorem replacementMonotone : RankedMultisetNormalizationTargets.ReplacementMonotone := by
  intro Symbol arity Gamma above removed inserted larger hin h
  revert h
  induction inserted with
  | nil => intro h; exact .nil larger
  | cons t rest ih =>
    intro h
    cases h with
    | cons removed s t rest hm hg hr => exact .cons larger s t rest (hin s hm) hg (ih hr)

private theorem prependGreater {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Tree Symbol arity Gamma}
    {ss ts kept retained removed inserted : List (Tree Symbol arity Gamma)}
    (hg : Greater Symbol arity Gamma above s t)
    (hs : ss.Perm (kept++removed)) (ht : ts.Perm (retained++inserted))
    (hk : EqualMatch Symbol arity Gamma kept retained)
    (hr : Replacement Symbol arity Gamma above removed inserted) :
    MultisetGreater Symbol arity Gamma above (s::ss) (t::ts) := by
  apply MultisetGreater.replace (s::ss) (t::ts) kept retained (s::removed) (t::inserted)
  · exact (hs.cons s).trans List.perm_middle.symm
  · exact (ht.cons t).trans List.perm_middle.symm
  · exact List.cons_ne_nil s removed
  · exact hk
  · exact .cons _ s t _ (List.mem_cons_self ..) hg
      (replacementMonotone Symbol arity Gamma above removed inserted (s::removed)
        (fun x hx => List.mem_cons_of_mem s hx) hr)

theorem weakMatchingNormalization : RankedMultisetNormalizationTargets.WeakMatchingNormalization := by
  intro Symbol arity Gamma above ss ts h
  induction h with
  | nil => exact Or.inl .nil
  | @cons s t ss ts hq hr ih =>
    cases hq with
    | equal s t he =>
      rcases ih with hk | hm
      · exact Or.inl (.cons s t ss ts he hk)
      · cases hm with
        | replace ss ts kept retained removed inserted hs ht hn hk hm =>
          exact Or.inr (.replace (s::ss) (t::ts) (s::kept) (t::retained) removed inserted
            (hs.cons s) (ht.cons t) hn (.cons s t kept retained he hk) hm)
    | greater s t hg =>
      rcases ih with hk | hm
      · exact Or.inr (prependGreater above hg (by simp) (by simp) hk (.nil []))
      · cases hm with
        | replace ss ts kept retained removed inserted hs ht hn hk hm =>
          exact Or.inr (prependGreater above hg hs ht hk hm)

private theorem replacementAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {removed left right : List (Tree Symbol arity Gamma)}
    (hl : Replacement Symbol arity Gamma above removed left)
    (hr : Replacement Symbol arity Gamma above removed right) :
    Replacement Symbol arity Gamma above removed (left++right) := by
  revert hl
  induction left with
  | nil => intro hl; exact hr
  | cons t rest ih =>
    intro hl
    cases hl with
    | cons removed s t rest hm hg hl => exact .cons _ s t _ hm hg (ih hl)

theorem generalizedMultisetNormalization : RankedMultisetNormalizationTargets.GeneralizedMultisetNormalization := by
  intro Symbol arity Gamma above ss ts kept retained removed inserted hs ht hn hw hr
  rcases weakMatchingNormalization Symbol arity Gamma above kept retained hw with he | hm
  · exact .replace ss ts kept retained removed inserted hs ht hn he hr
  · cases hm with
    | replace kept retained k r d i hk hret hd he hdi =>
      apply MultisetGreater.replace ss ts k r (d++removed) (i++inserted)
      · simpa only [List.append_assoc] using hs.trans (hk.append_right removed)
      · simpa only [List.append_assoc] using ht.trans (hret.append_right inserted)
      · intro hz
        have hzlen := congrArg List.length hz
        simp only [List.length_append,List.length_nil] at hzlen
        have hrlen : removed.length=0 := by omega
        exact hn (List.length_eq_zero_iff.mp hrlen)
      · exact he
      · apply replacementAppend above
        · exact replacementMonotone Symbol arity Gamma above d i (d++removed)
            (fun x hx => List.mem_append_left removed hx) hdi
        · exact replacementMonotone Symbol arity Gamma above removed inserted (d++removed)
            (fun x hx => List.mem_append_right d hx) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedMultisetNormalizationProof
