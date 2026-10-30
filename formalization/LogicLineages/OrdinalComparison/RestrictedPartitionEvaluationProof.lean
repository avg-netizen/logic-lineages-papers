module

public import LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationTargets
public import LogicLineages.OrdinalComparison.RestrictedPartitionCountProof
public import Mathlib.Data.List.GetD

@[expose] public section
namespace LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationProof

 theorem restrictedPartitionZeroDegreeCount : Targets.RestrictedPartitionZeroDegreeCount := by
  intro n
  classical
  by_cases hn : n = 0
  · subst n
    let e : RestrictedPartitionState 0 0 ≃ Unit := {
      toFun := fun _ => ()
      invFun := fun _ => ⟨fun i => Fin.elim0 i, by simp [restrictedPartitionWeight]⟩
      left_inv := by intro a; apply Subtype.ext; funext i; exact Fin.elim0 i
      right_inv := by intro u; cases u; rfl }
    simp only [restrictedPartitionCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_unit, ↓reduceIte]
  · letI : IsEmpty (RestrictedPartitionState 0 n) := ⟨fun a => by
      have h := a.2
      simp only [restrictedPartitionWeight, Fin.sum_univ_zero] at h
      exact hn h.symm⟩
    simp [restrictedPartitionCount, hn]

 theorem restrictedPartitionRowZeroConvention : Targets.RestrictedPartitionRowZeroConvention := by
  intro previous n
  simp [restrictedPartitionRowEntry]

private theorem map_range_getD (f : Nat → Nat) (N n : Nat) (hn : n < N) :
    ((List.range N).map f).getD n 0 = f n := by
  rw [List.getD_eq_getElem _ 0 (by simpa using hn)]
  simp

private theorem fold_sum_range (f : Nat → Nat) (N : Nat) :
    ((List.range N).map f).foldr (· + ·) 0 = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.foldr_append,
      List.foldr_cons, List.foldr_nil, Nat.add_zero, Finset.sum_range_succ]
    have h : ∀ l : List Nat, l.foldr (· + ·) (f N) = l.foldr (· + ·) 0 + f N := by
      intro l
      induction l with
      | nil => simp
      | cons a l hl => simp [hl, Nat.add_assoc]
    rw [h, ih]

 theorem restrictedPartitionRowsCorrect : Targets.RestrictedPartitionRowsCorrect := by
  intro bound d
  induction d with
  | zero =>
    constructor
    · simp [restrictedPartitionRows]
    · intro n hn
      rw [restrictedPartitionRows, map_range_getD _ _ _ (by omega), restrictedPartitionZeroDegreeCount]
  | succ d ih =>
    constructor
    · simp [restrictedPartitionRows, restrictedPartitionRowStep, ih.1]
    · intro n hn
      change ((List.range (restrictedPartitionRows bound d).length).map
        (restrictedPartitionRowEntry (d + 1) (restrictedPartitionRows bound d))).getD n 0 = _
      rw [map_range_getD _ _ _ (by rw [ih.1]; omega)]
      simp only [restrictedPartitionRowEntry, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      rw [fold_sum_range, restrictedPartitionLastCoordinateRecurrence]
      apply Finset.sum_congr rfl
      intro j hj
      exact ih.2 _ (Nat.le_trans (Nat.sub_le _ _) hn)

 theorem restrictedPartitionEvaluatorExact : Targets.RestrictedPartitionEvaluatorExact := by
  intro d n
  exact (restrictedPartitionRowsCorrect n d).2 n (Nat.le_refl n)

private theorem pr_rowEntry : Primrec (fun z : Nat × List Nat × Nat =>
    restrictedPartitionRowEntry z.1 z.2.1 z.2.2) := by
  have hk : Primrec (fun z : Nat × List Nat × Nat => z.1) := Primrec.fst
  have hp : Primrec (fun z : Nat × List Nat × Nat => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : Nat × List Nat × Nat => z.2.2) := Primrec.snd.comp Primrec.snd
  have hr := Primrec.list_range.comp (Primrec.succ.comp (Primrec.nat_div.comp hn hk))
  have he : Primrec₂ (fun z : Nat × List Nat × Nat => fun j : Nat =>
      z.2.1.getD (z.2.2 - z.1 * j) 0) :=
    ((Primrec.list_getD 0).comp (hp.comp Primrec.fst)
      (Primrec.nat_sub.comp (hn.comp Primrec.fst)
        (Primrec.nat_mul.comp (hk.comp Primrec.fst) Primrec.snd))).to₂
  have hm := Primrec.list_map hr he
  have hs := Primrec.list_foldr hm (Primrec.const 0)
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
    ((Primrec.list_getD 0).comp hp hn) hs

private theorem pr_rowStep : Primrec₂ restrictedPartitionRowStep := by
  have hr : Primrec (fun z : Nat × List Nat => List.range z.2.length) :=
    Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)
  have he : Primrec₂ (fun z : Nat × List Nat => fun n : Nat =>
      restrictedPartitionRowEntry z.1 z.2 n) :=
    (pr_rowEntry.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact (Primrec.list_map hr he).to₂

 theorem primitiveRecursivePartitionSteps : Targets.PrimitiveRecursivePartitionSteps :=
  ⟨pr_rowEntry, pr_rowStep⟩

private theorem pr_rows : Primrec₂ restrictedPartitionRows := by
  have hz : Primrec (fun bound : Nat =>
      (List.range (bound + 1)).map (fun n => if n = 0 then 1 else 0)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.succ)
      ((Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.const 1) (Primrec.const 0)).to₂)
  have hs : Primrec₂ (fun _ : Nat => fun z : Nat × List Nat =>
      restrictedPartitionRowStep (z.1 + 1) z.2) :=
    (pr_rowStep.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply (Primrec.nat_rec hz hs).of_eq
  intro bound d
  induction d with
  | zero => rfl
  | succ d ih => simpa only [Nat.rec_add_one, restrictedPartitionRows, ih]

 theorem primitiveRecursivePartitionEvaluator : Targets.PrimitiveRecursivePartitionEvaluator := by
  have he : Primrec₂ restrictedPartitionEval :=
    ((Primrec.list_getD 0).comp (pr_rows.comp Primrec.snd Primrec.fst) Primrec.snd).to₂
  exact ⟨pr_rows, he, he.of_eq restrictedPartitionEvaluatorExact⟩

end LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationProof
