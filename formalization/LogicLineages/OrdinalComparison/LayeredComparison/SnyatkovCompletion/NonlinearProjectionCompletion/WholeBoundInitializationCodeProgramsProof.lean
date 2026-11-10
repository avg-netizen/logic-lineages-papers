module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProof
open WholeBoundInitializationCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem contains_primitive : Primrec₂ (fun (bound : List Nat) (i : Nat) => bound.contains i) := by
  have hm : PrimrecRel (fun (bound : List Nat) (i : Nat) => ∃ j ∈ bound, j = i) :=
    (show PrimrecRel (fun a b : Nat => a = b) from Primrec.eq).exists_mem_list
  apply hm.decide.of_eq
  intro bound i
  by_cases h : i ∈ bound <;> simp [h]
#print axioms contains_primitive

theorem numeral_primitive : Primrec WindowCode.numeral :=
  Primrec.nat_mul.comp (Primrec.const 10) Primrec.id
#print axioms numeral_primitive

theorem step_computable : Computable (fun p : List Nat × (EntryData × RowData) =>
    step p.1 p.2.1 p.2.2) := by
  let C := List Nat × (EntryData × RowData)
  have hb : Primrec (fun p : C => p.1) := Primrec.fst
  have he : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have hw : Primrec (fun p : C => p.2.1.1) := Primrec.fst.comp he
  have ht : Primrec (fun p : C => p.2.1.2) := Primrec.snd.comp he
  have hn : Primrec (fun p : C => p.2.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp ht)
  have hterm : Computable (fun p : C => NormalForm.Code.itemTerm p.2.1.2) :=
    (NormalFormCodeProof.itemTerm_primitive.comp ht).to_comp
  have hp : Computable (fun p : C =>
      WindowCode.add (WindowCode.multiply p.2.1.1.toNat (NormalForm.Code.itemTerm p.2.1.2))
        p.2.2.1.1) :=
    BlockRowSubstitutionCodeProof.add_primitive.to_comp.comp
      (BlockRowSubstitutionCodeProof.multiply_primitive.to_comp.comp
        (BlockRowSubstitutionCodeProof.toNat_primitive.comp hw).to_comp hterm)
      (Primrec.fst.comp (Primrec.fst.comp hs)).to_comp
  have hm : Computable (fun p : C =>
      WindowCode.add (WindowCode.multiply (-p.2.1.1).toNat (NormalForm.Code.itemTerm p.2.1.2))
        p.2.2.1.2) :=
    BlockRowSubstitutionCodeProof.add_primitive.to_comp.comp
      (BlockRowSubstitutionCodeProof.multiply_primitive.to_comp.comp
        (BlockRowSubstitutionCodeProof.toNat_primitive.comp
          (IntegerAlgorithms.Proof.negate_primitive.comp hw)).to_comp hterm)
      (Primrec.snd.comp (Primrec.fst.comp hs)).to_comp
  have hkeep : Computable (fun p : C => (p.2.2.1, p.2.1 :: p.2.2.2)) :=
    (Primrec.fst.comp hs).to_comp.pair
      (Primrec.list_cons.comp he (Primrec.snd.comp hs)).to_comp
  have hmove : Computable (fun p : C =>
      ((WindowCode.add (WindowCode.multiply p.2.1.1.toNat (NormalForm.Code.itemTerm p.2.1.2))
          p.2.2.1.1,
        WindowCode.add (WindowCode.multiply (-p.2.1.1).toNat (NormalForm.Code.itemTerm p.2.1.2))
          p.2.2.1.2), p.2.2.2)) :=
    (hp.pair hm).pair (Primrec.snd.comp hs).to_comp
  simpa only [step, Bool.cond_decide] using
    Computable.cond
      (Primrec.eq.comp (contains_primitive.comp hb hn) (Primrec.const true)).decide.to_comp
      hkeep hmove
#print axioms step_computable
attribute [local irreducible] step

theorem entries_computable : Computable (fun p : List Nat × (Nat × (Nat × List EntryData)) =>
    entries p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let C := List Nat × (Nat × (Nat × List EntryData))
  have hf : Computable (fun p : C => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hg : Computable (fun p : C => ((p.2.1, p.2.2.1), ([] : List EntryData))) :=
    ((Computable.fst.comp Computable.snd).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair (Computable.const [])
  have hh : Computable₂ (fun p : C => fun q : EntryData × RowData => step p.1 q.1 q.2) := by
    change Computable (fun p : C × (EntryData × RowData) => step p.1.1 p.2.1 p.2.2)
    exact step_computable.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
  unfold entries
  exact ComparisonAssembly.computable_foldr (α := C) (β := EntryData) (σ := RowData)
    ((0 : Int), ((0 : Nat), (0 : Nat), (0 : Int), (0 : Int))) hf hg hh
#print axioms entries_computable
attribute [local irreducible] entries

theorem actualRowProgram : WholeBoundInitializationCodeTargets.ActualRowProgram := by
  change Computable (fun p : List Nat × NormalForm.Code.RowData => row p.1 p.2)
  unfold row
  have hz : Primrec (fun p : List Nat × NormalForm.Code.RowData => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hp := (numeral_primitive.comp (BlockRowSubstitutionCodeProof.toNat_primitive.comp hz)).to_comp
  have hn := (numeral_primitive.comp (BlockRowSubstitutionCodeProof.toNat_primitive.comp
    (IntegerAlgorithms.Proof.negate_primitive.comp hz))).to_comp
  exact entries_computable.comp (Computable.fst.pair
    (hp.pair (hn.pair (Computable.snd.comp Computable.snd))))
#print axioms actualRowProgram
attribute [local irreducible] row

theorem actualAtomProgram : WholeBoundInitializationCodeTargets.ActualAtomProgram := by
  change Computable (fun p : List Nat × NormalForm.Code.AtomData => atom p.1 p.2)
  unfold atom
  have hr : Computable (fun p : List Nat × NormalForm.Code.RowData => row p.1 p.2) :=
    actualRowProgram
  exact (Computable.fst.comp Computable.snd).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
      (hr.comp (Computable.fst.pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
#print axioms actualAtomProgram
attribute [local irreducible] atom

theorem decodeAtom_primitive : Primrec decodeAtom :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option NormalForm.Code.AtomData)))
    (Primrec.const (0, 0, (0 : Int), []))
#print axioms decodeAtom_primitive

theorem encodedAtom_computable : Computable₂ encodedAtom := by
  change Computable (fun p : List Nat × Nat => encodedAtom p.1 p.2)
  unfold encodedAtom
  have ha : Computable (fun p : List Nat × NormalForm.Code.AtomData => atom p.1 p.2) :=
    actualAtomProgram
  exact Computable.encode.comp (ha.comp (Computable.fst.pair
    (decodeAtom_primitive.to_comp.comp Computable.snd)))
#print axioms encodedAtom_computable
attribute [local irreducible] encodedAtom

theorem actualFormulaProgram : WholeBoundInitializationCodeTargets.ActualFormulaProgram := by
  change Computable₂ (fun bound code => LinearRows.Code.mapAtoms (encodedAtom bound) code)
  exact ComputableMapAtomsProof.actualJointMapProgram (List Nat) encodedAtom encodedAtom_computable
#print axioms actualFormulaProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProof
