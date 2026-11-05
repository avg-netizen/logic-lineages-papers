module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsControlResidueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsProof
open NormalForm MaximalPlainRows

private theorem residueSplit_remaining (i m : Nat) (xs : List (Int × Summand)) :
    (residueSplit i m xs).2 = xs.filter (fun a => retained i a.2) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      cases s with
      | «variable» j => simpa [residueSplit, retained] using ih
      | hyperPhi j e f => simpa [residueSplit, retained] using ih
      | phi j e =>
          by_cases hj : j = i <;> simp [residueSplit, retained, hj] at ih ⊢ <;> exact ih

theorem exactResidualOccurrences : MaximalPlainRowsTargets.ExactResidualOccurrences :=
  fun i m r => residueSplit_remaining i m r.2

private def folded (i m : Nat) (ν : Nat → Nat) (a : Int × Summand) : Int :=
  match a.2 with
  | .phi j _ => if j = i then a.1 * (fastControlResidue m : Int)
    else a.1 * (a.2.term.value ν : Int)
  | _ => a.1 * (a.2.term.value ν : Int)

private theorem residueSplit_value (i m : Nat) (xs : List (Int × Summand)) (ν : Nat → Nat) :
    (residueSplit i m xs).1 +
        ((residueSplit i m xs).2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      (xs.map (folded i m ν)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      cases s with
      | «variable» j =>
          simp only [residueSplit, List.foldr_cons, List.map_cons, List.sum_cons, folded] at ih ⊢
          omega
      | hyperPhi j e f =>
          simp only [residueSplit, List.foldr_cons, List.map_cons, List.sum_cons, folded] at ih ⊢
          omega
      | phi j e =>
          by_cases hj : j = i <;>
            simp only [residueSplit, List.foldr_cons, List.map_cons, List.sum_cons,
              folded, hj, if_true, if_false] at ih ⊢ <;> omega

private theorem member_le_sum (xs : List Nat) (x : Nat) (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y xs ih =>
      rcases List.mem_cons.mp h with h | h
      · subst y; simp
      · have hi := ih h
        simp only [List.sum_cons]
        omega

private theorem shift_lower (r : Row) (i m : Nat) (ν : Nat → Nat)
    (hb : PlainPhiDominance.shiftMass r + m ≤ ν i) (w e : Int)
    (ha : (w, Summand.phi i e) ∈ r.2) : m ≤ PlainPhiDominance.argument ν i e := by
  have he : e.natAbs ≤ PlainPhiDominance.shiftMass r := by
    apply member_le_sum
    exact List.mem_map.mpr ⟨(w, Summand.phi i e), ha, rfl⟩
  have hn := Int.le_natAbs (a := -e)
  have hz := Int.self_le_toNat ((ν i : Int) + e)
  simp only [Int.natAbs_neg] at hn
  unfold PlainPhiDominance.argument
  omega

private theorem sum_modEq (m : Int) (xs : List (Int × Summand))
    (f g : Int × Summand → Int) (h : ∀ a ∈ xs, Int.ModEq m (f a) (g a)) :
    Int.ModEq m (xs.map f).sum (xs.map g).sum := by
  induction xs with
  | nil => exact Int.ModEq.refl _
  | cons a xs ih =>
      exact (h a List.mem_cons_self).add (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem actualSignedRowResidue : MaximalPlainRowsTargets.ActualSignedRowResidue := by
  intro i m hm r ν hb
  have hsum : Int.ModEq (m : Int)
      (r.2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum
      (r.2.map (folded i m ν)).sum := by
    apply sum_modEq
    intro a ha
    rcases a with ⟨w, s⟩
    cases s with
    | «variable» j => exact Int.ModEq.refl _
    | hyperPhi j e f => exact Int.ModEq.refl _
    | phi j e =>
        by_cases hj : j = i
        · subst j
          have hn := shift_lower r i m ν hb w e ha
          have hnat := phi_shifted_residue m hm (PlainPhiDominance.argument ν i e) (by omega)
          have hz := Int.natCast_modEq_iff.mpr hnat
          have hw := hz.mul_left w
          simpa only [folded, if_pos rfl, if_true, Summand.term, Term.value,
            WindowProof.shifted_value, PlainPhiDominance.argument] using hw
        · simpa only [folded, if_neg hj] using
            (Int.ModEq.refl (w * ((Summand.phi j e).term.value ν : Int)) (n := (m : Int)))
  have hvalue := residueSplit_value i m r.2 ν
  have htotal := hsum.add_left r.1
  have he : rowValue (residueRow i m r) ν = r.1 + (r.2.map (folded i m ν)).sum := by
    simp only [residueRow, rowValue]
    omega
  rw [he]
  exact htotal

theorem residueRow_linear (i m : Nat) (r : Row) (hp : PlainPhiDominance.isPlain r = true) :
    LinearRows.rowLinear i (residueRow i m r) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  rw [exactResidualOccurrences] at ha
  have hs := List.mem_filter.mp ha
  have hplain := List.all_eq_true.mp hp a hs.1
  rcases a with ⟨w, s⟩
  cases s with
  | «variable» j => rfl
  | hyperPhi j e f => simp at hplain
  | phi j e => exact hs.2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsProof
