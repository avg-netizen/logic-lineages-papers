module
public import LogicLineages.OrdinalComparison.FiniteCoefficientCodingTargets
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem finiteCoefficientCodingPrimitiveRecursive : Targets.FiniteCoefficientCodingPrimitiveRecursive := by
  have hs : Primrec₂ (fun (p : Nat × List Nat) (q : Nat × Nat) => q.1+p.1*q.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  have hfold : Primrec₂ finiteCoefficientSlope :=
    Primrec.list_foldr (f := fun p : Nat × List Nat => p.2)
      (g := fun _ : Nat × List Nat => (0 : Nat))
      (h := fun (p : Nat × List Nat) (q : Nat × Nat) => q.1+p.1*q.2)
      Primrec.snd (Primrec.const 0) hs
  have hm : Primrec (fun xs : List Nat => xs.foldr max 0) :=
    Primrec.list_foldr (f := fun xs : List Nat => xs)
      (g := fun _ : List Nat => (0 : Nat))
      (h := fun (_ : List Nat) (q : Nat × Nat) => max q.1 q.2)
      Primrec.id (Primrec.const 0) (Primrec.nat_max.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact ⟨hfold, Primrec.nat_max.comp (Primrec.const 2)
    (Primrec.nat_add.comp (hm.comp Primrec.list_flatten) (Primrec.const 1))⟩

theorem finiteCoefficientSlopeCalibration : Targets.FiniteCoefficientSlopeCalibration := by
  constructor
  · intro B xs
    have h : finiteCoefficientSlope B xs=Nat.ofDigits B xs := by
      rw [Nat.ofDigits_eq_foldr]
      rfl
    exact ⟨h, h.trans (Nat.ofDigits_eq_sum_mapIdx B xs)⟩
  · intro B hB i
    exact pow_pos (by omega : 0<B) i

private theorem digit_le_max_fold (xs : List Nat) (a : Nat) (ha : a∈xs) :
    a≤xs.foldr max 0 := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_max_left _ _
    · exact (ih ha).trans (Nat.le_max_right _ _)

theorem finiteCoefficientFamilySeparation : Targets.FiniteCoefficientFamilySeparation := by
  intro rows
  have hbase : 2≤finiteCoefficientBase rows := Nat.le_max_left _ _
  have hd : ∀ xs∈rows, ∀ a∈xs, a<finiteCoefficientBase rows := by
    intro xs hxs a ha
    have hm := digit_le_max_fold rows.flatten a (List.mem_flatten.mpr ⟨xs,hxs,ha⟩)
    have hb : rows.flatten.foldr max 0+1≤finiteCoefficientBase rows := Nat.le_max_right _ _
    omega
  refine ⟨hbase, hd, ?_⟩
  intro xs hxs ys hys hlen
  constructor
  · intro h
    apply Nat.ofDigits_inj_of_len_eq (by omega : 1<finiteCoefficientBase rows) hlen (hd xs hxs) (hd ys hys)
    rw [← (finiteCoefficientSlopeCalibration.1 _ xs).1,
      ← (finiteCoefficientSlopeCalibration.1 _ ys).1]
    exact h
  · intro h
    rw [h]

end LogicLineages.OrdinalComparison
