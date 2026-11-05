module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsCompilerProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsProof
open MaximalPlainBranchPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] LinearRows.Code.decodeAtom
  PlainPhiDominance.Code.isPlain MaximalPlainPrograms.Code.cutoff

theorem isPlain_primitive : Primrec Code.isPlain := by
  have hp : Primrec₂ (fun (_ : Unit) a => PlainPhiDominance.Code.isPlain
      (LinearRows.Code.decodeAtom a).2.2) :=
    PlainPhiDominanceProof.isPlain_primitive.comp
      (Primrec.snd.comp (Primrec.snd.comp (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd)))
  exact (LinearRowsCodeProof.listAll_primitive hp).comp (Primrec.const ()) LinearRowsCodeProof.atoms_primitive

private theorem rowNames_primitive : Primrec (fun r : NormalForm.Code.RowData => r.2.map (fun b => b.2.2.1)) :=
  Primrec.list_map Primrec.snd
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂

theorem variables_primitive : Primrec Code.variables := by
  have hp : Primrec₂ (fun (_ : Nat) a =>
      (LinearRows.Code.decodeAtom a).2.2.2.map (fun b => b.2.2.1)) :=
    rowNames_primitive.comp
      (Primrec.snd.comp (Primrec.snd.comp (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd)))
  exact Primrec.list_flatMap LinearRowsCodeProof.atoms_primitive hp

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

theorem cutoff_primitive : Primrec Code.cutoff := by
  have hp : Primrec₂ (fun (_ : Nat) a => MaximalPlainPrograms.Code.cutoff (LinearRows.Code.decodeAtom a)) :=
    MaximalPlainProgramsProof.cutoff_primitive.comp (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd)
  exact naturalSum_primitive.comp (Primrec.list_map LinearRowsCodeProof.atoms_primitive hp)

theorem actualDataPrograms : MaximalPlainBranchProgramsTargets.ActualDataPrograms :=
  ⟨isPlain_primitive, variables_primitive, cutoff_primitive⟩

theorem lowerGuard_primitive : Primrec₂ Code.lowerGuard := by
  have hr : Primrec (fun p : Nat × Nat =>
      (-(p.2 : Int), [((1 : Int), (0, p.1, (0 : Int), (0 : Int)))])) :=
    (IntegerAlgorithms.Proof.negate_primitive.comp (IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.snd)).pair
      (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair
        ((Primrec.const 0).pair (Primrec.fst.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))))
        (Primrec.const []))
  exact ShiftedInputProgramsProof.atom_primitive.comp hr

theorem maximumGuard_primitive : Primrec₂ Code.maximumGuard := by
  have hv : Primrec₂ (fun (i j : Nat) =>
      ((0 : Int), [(1, (0, i, (0 : Int), (0 : Int))), (-1, (0, j, (0 : Int), (0 : Int)))])) :=
    (Primrec.const (0 : Int)).pair
      (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair
        ((Primrec.const 0).pair (Primrec.fst.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))))
        (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair
          ((Primrec.const 0).pair (Primrec.snd.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))))
          (Primrec.const [])))
  exact ShiftedInputProgramsProof.atom_primitive.comp hv

theorem frame_primitive : Primrec₂ Code.frame := by
  let A := Nat × Nat
  have hs : Primrec (fun p : A × (Nat × Nat) =>
      ShiftedInputPrograms.Code.conjunction (Code.maximumGuard p.1.1 p.2.1) p.2.2) :=
    ShiftedInputProgramsProof.conjunction_primitive.comp
      (maximumGuard_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A => (Code.variables p.2).foldr
      (fun j rest => ShiftedInputPrograms.Code.conjunction (Code.maximumGuard p.1 j) rest) 0) :=
    Primrec.list_foldr (variables_primitive.comp Primrec.snd) (Primrec.const 0) hs.to₂
  exact ShiftedInputProgramsProof.conjunction_primitive.comp
    (lowerGuard_primitive.comp Primrec.fst (cutoff_primitive.comp Primrec.snd)) hf

theorem actualFramePrograms : MaximalPlainBranchProgramsTargets.ActualFramePrograms :=
  ⟨lowerGuard_primitive, maximumGuard_primitive, frame_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsProof
