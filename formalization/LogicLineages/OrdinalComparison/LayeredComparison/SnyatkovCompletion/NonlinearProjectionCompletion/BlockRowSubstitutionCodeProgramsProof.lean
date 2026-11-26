module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProgramsProof
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeProof
open BlockRowSubstitutionCode

-- The accepted term recursion is already irreducible. Keep the numeric
-- pairing decoder opaque while composing the existing encoded programs.
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem add_primitive : Primrec₂ WindowCode.add :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) Primrec₂.natPair)
    (Primrec.const 2)
#print axioms add_primitive

theorem multiply_primitive : Primrec₂ WindowCode.multiply :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) Primrec₂.natPair)
    (Primrec.const 4)
#print axioms multiply_primitive

theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) IntegerAlgorithms.Proof.abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl
#print axioms toNat_primitive

theorem decodeRow_primitive : Primrec decodeRow :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option RowData)))
    (Primrec.const ((0, 0), []))
#print axioms decodeRow_primitive

theorem step_computable : Computable (fun p : Nat × (Nat × (EntryData × RowData)) =>
    step p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let C := Nat × (Nat × (EntryData × RowData))
  have hi : Primrec (fun p : C => p.1) := Primrec.fst
  have hr : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : C => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : C => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec (fun p : C => p.2.2.1.1) := Primrec.fst.comp he
  have ht : Primrec (fun p : C => p.2.2.1.2) := Primrec.snd.comp he
  have hn : Primrec (fun p : C => p.2.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp ht)
  have hc : Computable (fun p : C => WindowCode.termSubstitute p.1 p.2.1
      (NormalForm.Code.itemTerm p.2.2.1.2)) :=
    WindowCodeProof.term_computable.comp
      ((NormalFormCodeProof.itemTerm_primitive.comp ht).to_comp.pair
        (hi.to_comp.pair hr.to_comp))
  have hp : Computable (fun p : C => WindowCode.add
      (WindowCode.multiply p.2.2.1.1.toNat
        (WindowCode.termSubstitute p.1 p.2.1 (NormalForm.Code.itemTerm p.2.2.1.2)))
      p.2.2.2.1.1) :=
    add_primitive.to_comp.comp
      (multiply_primitive.to_comp.comp (toNat_primitive.comp hw).to_comp hc)
      (Primrec.fst.comp (Primrec.fst.comp hs)).to_comp
  have hm : Computable (fun p : C => WindowCode.add
      (WindowCode.multiply (-p.2.2.1.1).toNat
        (WindowCode.termSubstitute p.1 p.2.1 (NormalForm.Code.itemTerm p.2.2.1.2)))
      p.2.2.2.1.2) :=
    add_primitive.to_comp.comp
      (multiply_primitive.to_comp.comp
        (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp hw)).to_comp hc)
      (Primrec.snd.comp (Primrec.fst.comp hs)).to_comp
  have hyes : Computable (fun p : C =>
      ((WindowCode.add (WindowCode.multiply p.2.2.1.1.toNat
          (WindowCode.termSubstitute p.1 p.2.1 (NormalForm.Code.itemTerm p.2.2.1.2)))
          p.2.2.2.1.1,
        WindowCode.add (WindowCode.multiply (-p.2.2.1.1).toNat
          (WindowCode.termSubstitute p.1 p.2.1 (NormalForm.Code.itemTerm p.2.2.1.2)))
          p.2.2.2.1.2), p.2.2.2.2)) :=
    (hp.pair hm).pair (Primrec.snd.comp hs).to_comp
  have hno : Computable (fun p : C => (p.2.2.2.1, p.2.2.1 :: p.2.2.2.2)) :=
    (Primrec.fst.comp hs).to_comp.pair
      (Primrec.list_cons.comp he (Primrec.snd.comp hs)).to_comp
  simpa only [step, Bool.cond_decide] using
    Computable.cond (Primrec.eq.comp hn hi).decide.to_comp hyes hno
#print axioms step_computable
attribute [local irreducible] step

theorem entryList_computable : Computable (fun p : EntryInput => p.2.2.2.2) :=
  Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
#print axioms entryList_computable

theorem entrySeed_computable : Computable (fun p : EntryInput =>
    ((p.2.2.1, p.2.2.2.1), ([] : List EntryData))) :=
  ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))).pair
    (Computable.const [])
#print axioms entrySeed_computable

theorem entryStep_computable : Computable₂ (fun p : EntryInput =>
    fun q : EntryData × RowData => step p.1 p.2.1 q.1 q.2) := by
  change Computable (fun p : EntryInput × (EntryData × RowData) =>
    step p.1.1 p.1.2.1 p.2.1 p.2.2)
  exact step_computable.comp ((Computable.fst.comp Computable.fst).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
#print axioms entryStep_computable

theorem actualEntryProgram : BlockRowSubstitutionCodeTargets.ActualEntryProgram := by
  change Computable (fun p : EntryInput =>
    entries p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  unfold entries
  exact ComparisonAssembly.computable_foldr (α := EntryInput) (β := EntryData) (σ := RowData)
    ((0 : Int), ((0 : Nat), (0 : Nat), (0 : Int), (0 : Int)))
    entryList_computable entrySeed_computable entryStep_computable
#print axioms actualEntryProgram
attribute [local irreducible] entries

theorem rowPositive_computable : Computable (fun p : RowInput =>
    WindowCode.termSubstitute p.1 p.2.1 p.2.2.1.1) := by
  have hd : Computable (fun p : RowInput => p.2.2) := Computable.snd.comp Computable.snd
  exact WindowCodeProof.term_computable.comp
    ((Computable.fst.comp (Computable.fst.comp hd)).pair
      (Computable.fst.pair (Computable.fst.comp Computable.snd)))
#print axioms rowPositive_computable

theorem rowNegative_computable : Computable (fun p : RowInput =>
    WindowCode.termSubstitute p.1 p.2.1 p.2.2.1.2) := by
  have hd : Computable (fun p : RowInput => p.2.2) := Computable.snd.comp Computable.snd
  exact WindowCodeProof.term_computable.comp
    ((Computable.snd.comp (Computable.fst.comp hd)).pair
      (Computable.fst.pair (Computable.fst.comp Computable.snd)))
#print axioms rowNegative_computable

theorem actualRowProgram : BlockRowSubstitutionCodeTargets.ActualRowProgram := by
  change Computable (fun p : RowInput => row p.1 p.2.1 p.2.2)
  unfold row
  have he : Computable (fun p : EntryInput =>
      entries p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := actualEntryProgram
  exact he.comp (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
    (rowPositive_computable.pair (rowNegative_computable.pair
      (Computable.snd.comp (Computable.snd.comp Computable.snd))))))
#print axioms actualRowProgram
attribute [local irreducible] row

theorem encodedInput_computable : Computable (fun p : EncodedInput =>
    (p.1, p.2.1, decodeRow p.2.2)) :=
  Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
    (decodeRow_primitive.to_comp.comp (Computable.snd.comp Computable.snd)))
#print axioms encodedInput_computable

theorem actualEncodedProgram : BlockRowSubstitutionCodeTargets.ActualEncodedProgram := by
  change Computable (fun p : EncodedInput => encoded p.1 p.2.1 p.2.2)
  unfold encoded
  have hr : Computable (fun p : RowInput => row p.1 p.2.1 p.2.2) := actualRowProgram
  exact Computable.encode.comp (hr.comp encodedInput_computable)
#print axioms actualEncodedProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeProof
