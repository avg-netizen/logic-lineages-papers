import R1Calculator.CarlsonSupport
import Mathlib.Data.Finset.Lattice.Fold

/-! One finite lower cutoff stabilizes every positive and negative relation
atom to a later copied point. This is arithmetic, with actual ordinal labels. -/

noncomputable section
namespace R1Calculator.PureR1

theorem arithmeticR1_finite_anchor_cut (a : NONote) (ha : 0 < a.repr)
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < a.repr) :
    ∃ cut < a.repr, (∀ x ∈ X, x ≤ cut) ∧
      ∀ x ∈ X, ∀ y, cut < y → y < a.repr →
        (ArithmeticR1 x y ↔ ArithmeticR1 x a.repr) := by
  classical
  let note : (x : Ordinal.{0}) → x ∈ X → NONote :=
    fun x hx => Classical.choose (exists_nonote_repr_of_lt a (hX x hx))
  have hnote (x : Ordinal.{0}) (hx : x ∈ X) : (note x hx).repr = x :=
    Classical.choose_spec (exists_nonote_repr_of_lt a (hX x hx))
  let bound : Ordinal.{0} → Ordinal.{0} := fun x =>
    if hx : x ∈ X then
      if ArithmeticR1 x a.repr then x else (endpointNF (note x hx)).repr
    else 0
  have hbound (x : Ordinal.{0}) (hx : x ∈ X) : bound x < a.repr := by
    dsimp only [bound]
    rw [dif_pos hx]
    split_ifs with hr
    · exact hX x hx
    · have hneg : ¬ a.repr ≤ (endpointNF (note x hx)).repr := by
        intro hle
        apply hr
        exact ⟨note x hx, hnote x hx, (hX x hx).le, hle⟩
      exact lt_of_not_ge hneg
  let cut := X.sup bound
  have hcut : cut < a.repr := (Finset.sup_lt_iff ha).mpr hbound
  refine ⟨cut, hcut, ?_, ?_⟩
  · intro x hx
    have hb : x ≤ bound x := by
      dsimp only [bound]
      rw [dif_pos hx]
      split_ifs with hr
      · exact le_rfl
      · calc
          x = (note x hx).repr := (hnote x hx).symm
          _ ≤ (endpointNF (note x hx)).repr := repr_le_endpoint (note x hx).2
    exact hb.trans (Finset.le_sup hx)
  · intro x hx y hcy hya
    constructor
    · intro hxy
      by_contra hxa
      have he : (endpointNF (note x hx)).repr ≤ cut := by
        have hb := Finset.le_sup (f := bound) hx
        simpa only [bound, dif_pos hx, if_neg hxa] using hb
      have hyend : y ≤ (endpointNF (note x hx)).repr := by
        rw [← hnote x hx] at hxy
        exact ((arithmeticR1_note_iff (note x hx) y).mp hxy).2
      exact (not_lt_of_ge (hyend.trans he)) hcy
    · intro hxa
      have hxc : x ≤ cut := by
        have hb : x ≤ bound x := by
          simpa only [bound, dif_pos hx, if_pos hxa] using (le_rfl : x ≤ x)
        exact hb.trans (Finset.le_sup hx)
      exact arithmeticR1_between hxa (hxc.trans hcy.le) hya.le

#print axioms arithmeticR1_finite_anchor_cut

end R1Calculator.PureR1
