module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsMaskProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsProof
open NormalForm InactivePhiPrograms

theorem guard_primitive : Primrec₂ Code.guard := by
  have hd : Primrec (fun p : NormalForm.Code.RowData × List Bool => Code.dropped p.1 p.2) :=
    dropped_primitive
  exact ShiftedInputProgramsProof.canceled_primitive.comp hd

theorem withRow_primitive : Primrec₂ Code.withRow :=
  (Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

theorem atom_primitive : Primrec InactivePhiPrograms.Code.atom :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.encode) (Primrec.const 2)

theorem any_primitive : Primrec Code.any :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (ShiftedInputProgramsProof.disjunction_primitive.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem compileAtom_primitive : Primrec₂ Code.compileAtom := by
  let A := Nat × NormalForm.Code.AtomData
  have hr : Primrec (fun p : A => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun p : A => Code.masks p.1 p.2.2.2) :=
    masks_primitive.comp Primrec.fst hr
  have he : Primrec (fun p : A × List Bool =>
      ShiftedInputPrograms.Code.conjunction (Code.guard p.1.2.2.2 p.2)
        (InactivePhiPrograms.Code.atom (Code.withRow p.1.2 (Code.remaining p.1.2.2.2 p.2)))) :=
    ShiftedInputProgramsProof.conjunction_primitive.comp
      (guard_primitive.comp (hr.comp Primrec.fst) Primrec.snd)
      (atom_primitive.comp (withRow_primitive.comp (Primrec.snd.comp Primrec.fst)
        (remaining_primitive.comp (hr.comp Primrec.fst) Primrec.snd)))
  exact any_primitive.comp (Primrec.list_map hm he.to₂)

theorem actualCompilerPrograms : InactivePhiProgramsTargets.ActualCompilerPrograms :=
  ⟨guard_primitive, any_primitive, compileAtom_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsProof
