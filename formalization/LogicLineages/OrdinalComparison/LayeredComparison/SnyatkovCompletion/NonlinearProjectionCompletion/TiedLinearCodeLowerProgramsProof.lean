module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeLiftProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem decodeItem_primitive : Primrec decodeItem :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option NormalForm.Code.ItemData)))
    (Primrec.const (variableItem 0))
#print axioms decodeItem_primitive

theorem lowerSummand_primitive : Primrec (fun p : (List TokenData × Nat) × NormalForm.Code.ItemData =>
    lowerSummand p.1.1 p.1.2 p.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (tokenOfName_primitive.comp (Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.const (0, WindowCode.numeral 0))
#print axioms lowerSummand_primitive
attribute [local irreducible] lowerSummand

theorem lowerStep_primitive : Primrec (fun p : (List TokenData × Nat) ×
    (BlockRowSubstitutionCode.EntryData × BlockRowSubstitutionCode.RowData) =>
    lowerStep p.1.1 p.1.2 p.2.1 p.2.2) := by
  let C := (List TokenData × Nat) × (BlockRowSubstitutionCode.EntryData × BlockRowSubstitutionCode.RowData)
  have he : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have hw : Primrec (fun p : C => p.2.1.1) := Primrec.fst.comp he
  have ht : Primrec (fun p : C => lowerSummand p.1.1 p.1.2 p.2.1.2) :=
    lowerSummand_primitive.comp (Primrec.fst.pair (Primrec.snd.comp he))
  have hp : Primrec (fun p : C => WindowCode.add
      (WindowCode.multiply p.2.1.1.toNat (lowerSummand p.1.1 p.1.2 p.2.1.2).2) p.2.2.1.1) :=
    BlockRowSubstitutionCodeProof.add_primitive.comp
      (BlockRowSubstitutionCodeProof.multiply_primitive.comp
        (BlockRowSubstitutionCodeProof.toNat_primitive.comp hw) (Primrec.snd.comp ht))
      (Primrec.fst.comp (Primrec.fst.comp hr))
  have hn : Primrec (fun p : C => WindowCode.add
      (WindowCode.multiply (-p.2.1.1).toNat (lowerSummand p.1.1 p.1.2 p.2.1.2).2) p.2.2.1.2) :=
    BlockRowSubstitutionCodeProof.add_primitive.comp
      (BlockRowSubstitutionCodeProof.multiply_primitive.comp
        (BlockRowSubstitutionCodeProof.toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp hw))
        (Primrec.snd.comp ht)) (Primrec.snd.comp (Primrec.fst.comp hr))
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ht) (Primrec.const 0))
    ((hp.pair hn).pair (Primrec.snd.comp hr))
    ((Primrec.fst.comp hr).pair
      (Primrec.list_cons.comp (hw.pair (decodeItem_primitive.comp (Primrec.snd.comp ht)))
        (Primrec.snd.comp hr)))
#print axioms lowerStep_primitive
attribute [local irreducible] lowerStep

theorem lowerEntries_primitive : Primrec (fun p : (List TokenData × Nat) ×
    (Nat × (Nat × List BlockRowSubstitutionCode.EntryData)) =>
    lowerEntries p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let C := (List TokenData × Nat) × (Nat × (Nat × List BlockRowSubstitutionCode.EntryData))
  have hf : Primrec (fun p : C => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hg : Primrec (fun p : C => ((p.2.1, p.2.2.1), ([] : List BlockRowSubstitutionCode.EntryData))) :=
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair (Primrec.const [])
  have hh : Primrec (fun p : C × (BlockRowSubstitutionCode.EntryData × BlockRowSubstitutionCode.RowData) =>
      lowerStep p.1.1.1 p.1.1.2 p.2.1 p.2.2) :=
    lowerStep_primitive.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.list_foldr hf hg hh.to₂
#print axioms lowerEntries_primitive
attribute [local irreducible] lowerEntries

theorem lowerRow_primitive : Primrec (fun p : (List TokenData × Nat) × NormalForm.Code.RowData =>
    lowerRow p.1.1 p.1.2 p.2) := by
  have hz : Primrec (fun p : (List TokenData × Nat) × NormalForm.Code.RowData => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hp := WholeBoundInitializationCodeProof.numeral_primitive.comp
    (BlockRowSubstitutionCodeProof.toNat_primitive.comp hz)
  have hn := WholeBoundInitializationCodeProof.numeral_primitive.comp
    (BlockRowSubstitutionCodeProof.toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp hz))
  exact lowerEntries_primitive.comp (Primrec.fst.pair
    (hp.pair (hn.pair (Primrec.snd.comp Primrec.snd))))
#print axioms lowerRow_primitive
attribute [local irreducible] lowerRow

theorem lowerAtom_primitive : Primrec (fun p : (List TokenData × Nat) × NormalForm.Code.AtomData =>
    lowerAtom p.1.1 p.1.2 p.2) :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (lowerRow_primitive.comp (Primrec.fst.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
#print axioms lowerAtom_primitive
attribute [local irreducible] lowerAtom

theorem lowerEncodedAtom_primitive : Primrec (fun p : (List TokenData × Nat) × Nat =>
    lowerEncodedAtom p.1.1 p.1.2 p.2) :=
  Primrec.encode.comp (lowerAtom_primitive.comp
    (Primrec.fst.pair (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd)))
#print axioms lowerEncodedAtom_primitive
attribute [local irreducible] lowerEncodedAtom

theorem lowerFormula_computable : Computable (fun p : AdapterInput => lowerFormula p.1 p.2.1 p.2.2) := by
  have hm : Computable (fun p : (List TokenData × Nat) × Nat =>
      LinearRows.Code.mapAtoms (lowerEncodedAtom p.1.1 p.1.2) p.2) :=
    ComputableMapAtomsProof.actualJointMapProgram (List TokenData × Nat)
      (fun args code => lowerEncodedAtom args.1 args.2 code) lowerEncodedAtom_primitive.to_comp
  exact hm.comp ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
    (Computable.snd.comp Computable.snd))
#print axioms lowerFormula_computable

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
