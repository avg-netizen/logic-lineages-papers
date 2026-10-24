import Mathlib.SetTheory.Ordinal.Notation

/-!
# Actual ordinal witnesses below a normal notation

Every actual ordinal below the denotation of a normal notation has a normal
notation. The proof uses Mathlib's fundamental-sequence theorem and
well-founded induction on denotation; no epsilon-zero range or surjectivity
assumption is supplied. In particular finite semantic witness tuples can be
represented without first assuming that their coordinates are notations.

These are semantic existence theorems, not an algorithm taking an arbitrary
`Ordinal` value as executable input.
-/

namespace R1Calculator

/-- Initial-segment coverage for ACTUAL ordinals, not merely smaller notations. -/
theorem exists_nf_repr_of_lt : ∀ {b : ONote}, b.NF →
    ∀ {δ : Ordinal.{0}}, δ < b.repr → ∃ a : ONote, a.NF ∧ a.repr = δ := by
  intro b
  refine (InvImage.wf ONote.repr Ordinal.lt_wf).induction
    (C := fun b => b.NF → ∀ {δ : Ordinal.{0}}, δ < b.repr →
      ∃ a : ONote, a.NF ∧ a.repr = δ) b ?_
  intro b ih hb δ hδ
  have hs := ONote.fundamentalSequence_has_prop b
  rcases hfs : b.fundamentalSequence with (⟨_ | a⟩ | f) <;>
    rw [hfs, ONote.FundamentalSequenceProp] at hs
  · subst b
    simp at hδ
  · obtain ⟨hrep, hnf⟩ := hs
    have hab : a.repr < b.repr := by
      rw [hrep]
      exact Order.lt_succ _
    rw [hrep] at hδ
    rcases lt_or_eq_of_le (Order.le_of_lt_succ hδ) with hlt | heq
    · exact ih a hab (hnf hb) hlt
    · exact ⟨a, hnf hb, heq.symm⟩
  · obtain ⟨i, hi⟩ := hs.2.2 δ hδ
    exact ih (f i) (hs.2.1 i).2.1 ((hs.2.1 i).2.2 hb) hi

/-- Including the upper endpoint adds the original normal notation itself. -/
theorem exists_nf_repr_of_le {b : ONote} (hb : b.NF) {δ : Ordinal.{0}}
    (hδ : δ ≤ b.repr) : ∃ a : ONote, a.NF ∧ a.repr = δ := by
  rcases lt_or_eq_of_le hδ with hlt | heq
  · exact exists_nf_repr_of_lt hb hlt
  · exact ⟨b, hb, heq.symm⟩

theorem exists_nonote_repr_of_lt (b : NONote) {δ : Ordinal.{0}}
    (hδ : δ < b.repr) : ∃ a : NONote, a.repr = δ := by
  obtain ⟨a, ha, hrepr⟩ := exists_nf_repr_of_lt b.2 hδ
  exact ⟨⟨a, ha⟩, hrepr⟩

theorem exists_nonote_repr_of_le (b : NONote) {δ : Ordinal.{0}}
    (hδ : δ ≤ b.repr) : ∃ a : NONote, a.repr = δ := by
  obtain ⟨a, ha, hrepr⟩ := exists_nf_repr_of_le b.2 hδ
  exact ⟨⟨a, ha⟩, hrepr⟩

/-- Every finite ACTUAL semantic tuple below b has a normal-notation tuple
with exactly the same ordinal coordinates. Empty tuples are included. -/
theorem notation_tuple_coverage {n : Nat} (b : NONote)
    (x : Fin n → Ordinal.{0}) (hx : ∀ i, x i < b.repr) :
    ∃ a : Fin n → NONote, (∀ i, (a i).repr = x i) ∧ ∀ i, a i < b := by
  classical
  let a : Fin n → NONote := fun i =>
    Classical.choose (exists_nonote_repr_of_lt b (hx i))
  have heq (i : Fin n) : (a i).repr = x i :=
    Classical.choose_spec (exists_nonote_repr_of_lt b (hx i))
  refine ⟨a, heq, ?_⟩
  intro i
  change (a i).repr < b.repr
  rw [heq]
  exact hx i

/-- Normal notations with the same actual denotation have the same label. -/
theorem nonote_eq_of_repr_eq {a b : NONote} (h : a.repr = b.repr) : a = b := by
  apply le_antisymm
  · exact h.le
  · exact h.ge

/-- Bounded denotation is an order isomorphism onto the ENTIRE actual ordinal
initial segment. Its inverse fixes an existing normal label automatically. -/
noncomputable def initialSegmentOrderIso (b : NONote) :
    {a : NONote // a < b} ≃o {δ : Ordinal.{0} // δ < b.repr} := by
  classical
  have point (x : {δ : Ordinal.{0} // δ < b.repr}) :
      ∃ a : {a : NONote // a < b}, a.val.repr = x.val := by
    obtain ⟨a, ha⟩ := exists_nonote_repr_of_lt b x.property
    have hab : a < b := by
      change a.repr < b.repr
      rw [ha]
      exact x.property
    exact ⟨⟨a, hab⟩, ha⟩
  exact
    { toFun := fun a => ⟨a.val.repr, a.property⟩
      invFun := fun x => Classical.choose (point x)
      left_inv := fun a => Subtype.ext (nonote_eq_of_repr_eq
        (Classical.choose_spec (point ⟨a.val.repr, a.property⟩)))
      right_inv := fun x => Subtype.ext (Classical.choose_spec (point x))
      map_rel_iff' := fun {_ _} => Iff.rfl }

@[simp] theorem initialSegmentOrderIso_apply (b : NONote)
    (a : {a : NONote // a < b}) :
    (initialSegmentOrderIso b a).val = a.val.repr := rfl

theorem initialSegmentOrderIso_symm_repr (b : NONote)
    (x : {δ : Ordinal.{0} // δ < b.repr}) :
    ((initialSegmentOrderIso b).symm x).val.repr = x.val := by
  exact congrArg Subtype.val ((initialSegmentOrderIso b).apply_symm_apply x)

#print axioms exists_nf_repr_of_lt
#print axioms exists_nonote_repr_of_lt
#print axioms notation_tuple_coverage
#print axioms initialSegmentOrderIso

end R1Calculator
