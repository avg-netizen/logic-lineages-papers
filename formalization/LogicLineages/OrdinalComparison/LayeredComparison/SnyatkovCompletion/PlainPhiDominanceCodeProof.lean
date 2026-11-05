module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
open NormalForm PlainPhiDominance

theorem isPlain_calibration (r : Row) : Code.isPlain (rowData r) = isPlain r := by
  simp only [Code.isPlain, isPlain, rowData, List.all_map, Function.comp_def]
  apply congrArg (fun f : Int × Summand → Bool => r.2.all f)
  funext a
  rcases a with ⟨w, s⟩
  cases s <;> rfl

theorem mass_calibration (r : Row) : Code.mass (rowData r) = mass r := by
  simp only [Code.mass, mass, rowData, List.map_map, Function.comp_def]

theorem shiftMass_calibration (r : Row) : Code.shiftMass (rowData r) = shiftMass r := by
  simp only [Code.shiftMass, shiftMass, rowData, List.map_map, Function.comp_def]
  apply congrArg (fun f : Int × Summand → Nat => (r.2.map f).sum)
  funext a
  rcases a with ⟨w, s⟩
  cases s <;> rfl

theorem threshold_calibration (r : Row) : Code.threshold (rowData r) = threshold r := by
  unfold Code.threshold threshold
  rw [mass_calibration, shiftMass_calibration]
  rfl

theorem literalThresholdCalibration : PlainPhiDominanceTargets.LiteralThresholdCalibration :=
  fun r => ⟨isPlain_calibration r, mass_calibration r,
    shiftMass_calibration r, threshold_calibration r⟩

private theorem naturalSum_primitive : Primrec (fun xs : List Nat => xs.sum) := by
  have hs : Primrec (fun p : List Nat × (Nat × Nat) => p.2.1 + p.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Nat => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

theorem isPlain_primitive : Primrec Code.isPlain := by
  have hp : Primrec₂ (fun (_ : Unit) (a : Int × NormalForm.Code.ItemData) =>
      decide (a.2.1 ≤ 1)) :=
    (Primrec.nat_le.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const 1)).decide
  exact (LinearRowsCodeProof.listAll_primitive hp).comp (Primrec.const ()) Primrec.snd

theorem mass_primitive : Primrec Code.mass := by
  have hp : Primrec₂ (fun (_ : NormalForm.Code.RowData) (a : Int × NormalForm.Code.ItemData) =>
      a.1.natAbs) :=
    IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp Primrec.snd)
  exact naturalSum_primitive.comp (Primrec.list_map Primrec.snd hp)

theorem shiftMass_primitive : Primrec Code.shiftMass := by
  let A := NormalForm.Code.RowData × (Int × NormalForm.Code.ItemData)
  have ht : Primrec (fun p : A => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : A => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hp : Primrec (fun p : A => if p.2.2.1 = 1 then p.2.2.2.2.1.natAbs else 0) :=
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 1))
      (IntegerAlgorithms.Proof.abs_primitive.comp he) (Primrec.const 0)
  exact naturalSum_primitive.comp (Primrec.list_map Primrec.snd hp.to₂)

theorem threshold_primitive : Primrec Code.threshold :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp shiftMass_primitive
          (Primrec.nat_mul.comp (Primrec.const 2) mass_primitive))
        (Primrec.nat_mul.comp mass_primitive shiftMass_primitive))
      (IntegerAlgorithms.Proof.abs_primitive.comp Primrec.fst))
    (Primrec.const 1)

theorem actualThresholdPrograms : PlainPhiDominanceTargets.ActualThresholdPrograms :=
  ⟨isPlain_primitive, mass_primitive, shiftMass_primitive, threshold_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
