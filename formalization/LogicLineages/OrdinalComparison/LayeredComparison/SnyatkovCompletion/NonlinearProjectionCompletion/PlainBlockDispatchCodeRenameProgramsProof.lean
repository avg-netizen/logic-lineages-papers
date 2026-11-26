module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeListProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem renameItem_primitive : Primrec (fun p : Nat × (Nat × NormalForm.Code.ItemData) => renameItem p.1 p.2.1 p.2.2) := by
  let A := Nat × (Nat × NormalForm.Code.ItemData)
  have hs : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun p : A => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp hs)
  have hr : Primrec (fun p : A => if p.2.2.2.1 = p.1 then p.2.1 else p.2.2.2.1) :=
    Primrec.ite (Primrec.eq.comp hn Primrec.fst) (Primrec.fst.comp Primrec.snd) hn
  exact (Primrec.fst.comp hs).pair (hr.pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))).pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs)))))
#print axioms renameItem_primitive

attribute [local irreducible] renameItem

theorem renameRow_primitive : Primrec (fun p : Nat × (Nat × RowData) => renameRow p.1 p.2.1 p.2.2) := by
  let A := Nat × (Nat × RowData)
  have he : Primrec (fun p : A × (Int × NormalForm.Code.ItemData) =>
      (p.2.1, renameItem p.1.1 p.1.2.1 p.2.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      (renameItem_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) he.to₂)
#print axioms renameRow_primitive

attribute [local irreducible] renameRow

theorem renameEncodedAtom_primitive : Primrec (fun p : (Nat × Nat) × Nat => renameEncodedAtom p.1.1 p.1.2 p.2) := by
  let A := (Nat × Nat) × Nat
  have ha : Primrec (fun p : A => BlockFormulaSubstitutionCode.decodeAtom p.2) :=
    BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp Primrec.snd
  have hr : Primrec (fun p : A => renameRow p.1.1 p.1.2 (BlockFormulaSubstitutionCode.decodeAtom p.2).2.2) :=
    renameRow_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp (Primrec.snd.comp ha))))
  exact Primrec.encode.comp ((Primrec.fst.comp ha).pair
    ((Primrec.fst.comp (Primrec.snd.comp ha)).pair hr))
#print axioms renameEncodedAtom_primitive

attribute [local irreducible] renameEncodedAtom

theorem rename_computable : Computable (fun p : Nat × (Nat × Nat) => rename p.1 p.2.1 p.2.2) := by
  have hm : Computable (fun p : (Nat × Nat) × Nat =>
      LinearRows.Code.mapAtoms (renameEncodedAtom p.1.1 p.1.2) p.2) :=
    ComputableMapAtomsProof.actualJointMapProgram (Nat × Nat)
      (fun args code => renameEncodedAtom args.1 args.2 code) renameEncodedAtom_primitive.to_comp
  exact hm.comp ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
    (Computable.snd.comp Computable.snd))
#print axioms rename_computable

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
