module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxTargets
public import Mathlib.Data.List.GetD
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof

/-- The literal recursive words contain exactly the positive tuples below L. -/
theorem words_spec (L n : Nat) (word : List Nat) :
    word ∈ singleCoreBoxWords L n ↔
      word.length = n ∧ ∀ v ∈ word, 0 < v ∧ v < L := by
  induction n generalizing word with
  | zero =>
    constructor
    · intro h
      have he : word = [] := List.mem_singleton.mp h
      subst word
      exact ⟨rfl, fun v hv => by cases hv⟩
    · rintro ⟨hlen, hvalues⟩
      have he : word = [] := List.eq_nil_of_length_eq_zero hlen
      subst word
      exact List.mem_singleton_self _
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨v, hv, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨rest, hrest, heq⟩ := List.mem_map.mp hm
      subst word
      have hr := (ih rest).mp hrest
      have hb := List.mem_range.mp hv
      refine ⟨by simp [hr.1], ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · exact hr.2 w hw
    · rintro ⟨hlen, hvalues⟩
      cases word with
      | nil => simp at hlen
      | cons v rest =>
        have hFirst := hvalues v List.mem_cons_self
        have hRest : rest ∈ singleCoreBoxWords L n := (ih rest).mpr
          ⟨by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen,
            fun w hw => hvalues w (List.mem_cons_of_mem _ hw)⟩
        apply List.mem_flatMap.mpr
        refine ⟨v - 1, List.mem_range.mpr (by omega), ?_⟩
        apply List.mem_map.mpr
        refine ⟨rest, hRest, ?_⟩
        rw [Nat.sub_add_cancel (by omega)]

/-- Empty support contributes one word, including when L is zero or one. -/
theorem words_empty (L : Nat) : singleCoreBoxWords L 0 = [[]] := rfl

/-- First-occurrence lookup agrees with the canonical map even with duplicates. -/
theorem lookup_map (support : List Nat) (ν : Nat → Nat) :
    ∀ i ∈ support, singleCoreBoxLookup support (support.map ν) i = ν i := by
  intro i hi
  have hidx : support.findIdx (fun j => decide (j = i)) < support.length :=
    List.findIdx_lt_length_of_exists ⟨i, hi, by simp⟩
  unfold singleCoreBoxLookup
  rw [List.getD_eq_getElem _ 1 (by simpa using hidx)]
  simp only [List.getElem_map]
  exact congrArg ν (of_decide_eq_true (List.findIdx_getElem (w := hidx)))

/-- The default is exactly one at every name absent from the support. -/
theorem lookup_outside (support word : List Nat) (hlen : word.length = support.length) :
    ∀ i, i ∉ support → singleCoreBoxLookup support word i = 1 := by
  intro i hi
  have hidx : support.findIdx (fun j => decide (j = i)) = support.length := by
    apply List.findIdx_eq_length_of_false
    intro j hj
    have hne : j ≠ i := by
      intro heq
      subst j
      exact hi hj
    simp only [decide_eq_false_iff_not]
    exact hne
  unfold singleCoreBoxLookup
  rw [hidx]
  exact List.getD_eq_default word 1 (Nat.le_of_eq hlen)

/-- Positive word entries give a globally positive valuation, via default one. -/
theorem lookup_positive (support word : List Nat) (h : ∀ v ∈ word, 0 < v)
    (i : Nat) : 0 < singleCoreBoxLookup support word i := by
  unfold singleCoreBoxLookup
  by_cases hb : support.findIdx (fun j => decide (j = i)) < word.length
  · rw [List.getD_eq_getElem word 1 hb]
    exact h _ (List.getElem_mem hb)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hb)]
    exact Nat.zero_lt_one

/-- Equal lengths ensure every support lookup selects a bounded word entry. -/
theorem lookup_bounded (L : Nat) (support word : List Nat)
    (hlen : word.length = support.length) (h : ∀ v ∈ word, v < L) :
    ∀ i ∈ support, singleCoreBoxLookup support word i < L := by
  intro i hi
  have hidx : support.findIdx (fun j => decide (j = i)) < support.length :=
    List.findIdx_lt_length_of_exists ⟨i, hi, by simp⟩
  have hword : support.findIdx (fun j => decide (j = i)) < word.length := by
    rw [hlen]
    exact hidx
  unfold singleCoreBoxLookup
  rw [List.getD_eq_getElem word 1 hword]
  exact h _ (List.getElem_mem hword)

theorem exactFiniteBox : Targets.ExactFiniteBox := by
  refine ⟨words_spec, words_empty, lookup_map, lookup_outside, ?_⟩
  intro L support word hword
  have hs := (words_spec L support.length word).mp hword
  exact ⟨lookup_positive support word (fun v hv => (hs.2 v hv).1),
    lookup_bounded L support word hs.1 (fun v hv => (hs.2 v hv).2)⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
