module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsGuardProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsResidueProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceCodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
open MaximalPlainPrograms

theorem nonnegative_primitive : Primrec₂ Code.nonnegative := by
  let A := Nat × NormalForm.Code.RowData
  have hi : Primrec (fun p : A => InactivePhiPrograms.Code.compileAtom p.1 (0, 0, p.2)) :=
    InactivePhiProgramsProof.compileAtom_primitive.comp Primrec.fst
      ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.snd))
  have hz : Primrec (fun p : A => ShiftedInputPrograms.Code.activeSign p.2 0) :=
    ShiftedInputProgramsProof.activeSign_primitive.comp Primrec.snd (Primrec.const 0)
  have hp : Primrec (fun p : A => ShiftedInputPrograms.Code.activeSign p.2 1) :=
    ShiftedInputProgramsProof.activeSign_primitive.comp Primrec.snd (Primrec.const 1)
  exact ShiftedInputProgramsProof.disjunction_primitive.comp hi
    (ShiftedInputProgramsProof.conjunction_primitive.comp activeGuard_primitive
      (ShiftedInputProgramsProof.disjunction_primitive.comp hz hp))

theorem cutoff_primitive : Primrec Code.cutoff :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (PlainPhiDominanceProof.threshold_primitive.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp
      (PlainPhiDominanceProof.shiftMass_primitive.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))

theorem compileAtom_primitive : Primrec₂ Code.compileAtom := by
  let A := Nat × NormalForm.Code.AtomData
  have ht : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : A => Code.residueRow p.1 (p.2.2.1 + 1) p.2.2.2) :=
    residueRow_primitive.comp (Primrec.fst.pair
      ((Primrec.nat_add.comp hm (Primrec.const 1)).pair hr))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
    (nonnegative_primitive.comp Primrec.fst hr)
    (InactivePhiProgramsProof.atom_primitive.comp ((Primrec.const 1).pair (hm.pair hs)))

theorem actualCompilerPrograms : MaximalPlainProgramsTargets.ActualCompilerPrograms :=
  ⟨cutoff_primitive, compileAtom_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
