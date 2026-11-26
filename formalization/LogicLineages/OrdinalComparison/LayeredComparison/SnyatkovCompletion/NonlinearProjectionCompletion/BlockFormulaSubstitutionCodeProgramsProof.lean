module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProof
open BlockFormulaSubstitutionCode

-- Compose the accepted programs without expanding their recursion or pairing decoder.
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair
attribute [local irreducible] BlockRowSubstitutionCode.row

theorem decodeAtom_primitive : Primrec decodeAtom :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option AtomData)))
    (Primrec.const (0, 0, ((0, 0), [])))
#print axioms decodeAtom_primitive

theorem actualAtomProgram : BlockFormulaSubstitutionCodeTargets.ActualAtomProgram := by
  change Computable (fun p : AtomInput => atom p.1 p.2.1 p.2.2)
  unfold atom
  have ha : Computable (fun p : AtomInput => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hr : Computable (fun p : BlockRowSubstitutionCode.RowInput =>
      BlockRowSubstitutionCode.row p.1 p.2.1 p.2.2) :=
    BlockRowSubstitutionCodeProof.actualRowProgram
  exact (Computable.fst.comp ha).pair ((Computable.fst.comp (Computable.snd.comp ha)).pair
    (hr.comp (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Computable.snd.comp (Computable.snd.comp ha))))))
#print axioms actualAtomProgram
attribute [local irreducible] atom

theorem encodedInput_computable : Computable (fun p : CodeInput =>
    (p.1, p.2.1, decodeAtom p.2.2)) :=
  Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
    (decodeAtom_primitive.to_comp.comp (Computable.snd.comp Computable.snd)))
#print axioms encodedInput_computable

theorem actualEncodedAtomProgram :
    BlockFormulaSubstitutionCodeTargets.ActualEncodedAtomProgram := by
  change Computable (fun p : CodeInput => encodedAtom p.1 p.2.1 p.2.2)
  unfold encodedAtom
  have ha : Computable (fun p : AtomInput => atom p.1 p.2.1 p.2.2) := actualAtomProgram
  exact Computable.encode.comp (ha.comp encodedInput_computable)
#print axioms actualEncodedAtomProgram
attribute [local irreducible] encodedAtom

theorem jointEncodedAtom_computable :
    Computable₂ (fun args : Nat × Nat => fun code : Nat => encodedAtom args.1 args.2 code) := by
  change Computable (fun p : (Nat × Nat) × Nat => encodedAtom p.1.1 p.1.2 p.2)
  have he : Computable (fun p : CodeInput => encodedAtom p.1 p.2.1 p.2.2) :=
    actualEncodedAtomProgram
  exact he.comp ((Computable.fst.comp Computable.fst).pair
    ((Computable.snd.comp Computable.fst).pair Computable.snd))
#print axioms jointEncodedAtom_computable

theorem actualFormulaProgram : BlockFormulaSubstitutionCodeTargets.ActualFormulaProgram := by
  change Computable (fun p : CodeInput => formula p.1 p.2.1 p.2.2)
  unfold formula
  have hm : Computable (fun p : (Nat × Nat) × Nat =>
      LinearRows.Code.mapAtoms (encodedAtom p.1.1 p.1.2) p.2) :=
    ComputableMapAtomsProof.actualJointMapProgram (Nat × Nat)
      (fun args code => encodedAtom args.1 args.2 code) jointEncodedAtom_computable
  exact hm.comp ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
    (Computable.snd.comp Computable.snd))
#print axioms actualFormulaProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProof
