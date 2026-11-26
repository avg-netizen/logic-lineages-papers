module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
open PlainBlockProjectionCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem add_primitive : Primrec₂ WindowCode.add := PlainBlockLinearizationCodeProof.binary_primitive 10 2
#print axioms add_primitive

theorem multiply_primitive : Primrec₂ WindowCode.multiply := PlainBlockLinearizationCodeProof.binary_primitive 10 4
#print axioms multiply_primitive

theorem negative_primitive : Primrec WindowCode.negative := PlainBlockLinearizationCodeProof.unary_primitive 8 5
#print axioms negative_primitive

theorem atMost_primitive : Primrec₂ WindowCode.atMost := negative_primitive.comp
  ((PlainBlockLinearizationCodeProof.binary_primitive 8 3).comp Primrec.snd Primrec.fst)
#print axioms atMost_primitive

theorem weightedFold_primitive (sign : Int → Nat) (hsg : Primrec sign) :
    Primrec (fun xs : List BlockRowSubstitutionCode.EntryData => xs.foldr
      (fun a rest => WindowCode.add (WindowCode.multiply (sign a.1) (NormalForm.Code.itemTerm a.2)) rest)
      (WindowCode.numeral 0)) := by
  have hs : Primrec (fun p : List BlockRowSubstitutionCode.EntryData × (BlockRowSubstitutionCode.EntryData × Nat) =>
      WindowCode.add (WindowCode.multiply (sign p.2.1.1) (NormalForm.Code.itemTerm p.2.1.2)) p.2.2) :=
    add_primitive.comp (multiply_primitive.comp
      (hsg.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (NormalFormCodeProof.itemTerm_primitive.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const (WindowCode.numeral 0)) hs.to₂
#print axioms weightedFold_primitive

theorem positiveTerm_primitive : Primrec positiveTerm := add_primitive.comp (Primrec.fst.comp Primrec.fst)
  ((weightedFold_primitive Int.toNat BlockRowSubstitutionCodeProof.toNat_primitive).comp Primrec.snd)
#print axioms positiveTerm_primitive

theorem negativeTerm_primitive : Primrec negativeTerm := add_primitive.comp (Primrec.snd.comp Primrec.fst)
  ((weightedFold_primitive (fun z => (-z).toNat)
    (BlockRowSubstitutionCodeProof.toNat_primitive.comp IntegerAlgorithms.Proof.negate_primitive)).comp Primrec.snd)
#print axioms negativeTerm_primitive

attribute [local irreducible] positiveTerm negativeTerm

theorem absoluteTerm_primitive : Primrec absoluteTerm := add_primitive.comp
  (PlainBlockLinearizationCodeProof.subtract_primitive.comp positiveTerm_primitive negativeTerm_primitive)
  (PlainBlockLinearizationCodeProof.subtract_primitive.comp negativeTerm_primitive positiveTerm_primitive)
#print axioms absoluteTerm_primitive

attribute [local irreducible] absoluteTerm

theorem atom_primitive : Primrec atom := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
  (atMost_primitive.comp (negativeTerm_primitive.comp (Primrec.snd.comp Primrec.snd))
    (positiveTerm_primitive.comp (Primrec.snd.comp Primrec.snd)))
  ((PlainBlockLinearizationCodeProof.binary_primitive 8 4).comp
    (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
    (absoluteTerm_primitive.comp (Primrec.snd.comp Primrec.snd)))
#print axioms atom_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
