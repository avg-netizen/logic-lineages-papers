module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeRowProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
open PlainBlockLinearizationCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair


theorem upperBoundaryGuard_primitive : Primrec (fun p : Nat × RowData =>
    nonnegative ((WindowCode.numeral 0, WindowCode.add (boundary p.1 p.2) (WindowCode.numeral 3)),
      [(1, TiedLinearCode.variableItem p.1)])) :=
  nonnegative_primitive.comp (((Primrec.const (WindowCode.numeral 0)).pair
    (BlockRowSubstitutionCodeProof.add_primitive.comp boundary_primitive (Primrec.const (WindowCode.numeral 3)))).pair
    (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair
      (TiedLinearCodeProof.variableItem_primitive.comp Primrec.fst)) (Primrec.const [])))
#print axioms upperBoundaryGuard_primitive

theorem lowerBoundaryGuard_primitive : Primrec (fun p : Nat × RowData =>
    nonnegative ((WindowCode.subtract (boundary p.1 p.2) (WindowCode.numeral 2), WindowCode.numeral 1),
      [(-1, TiedLinearCode.variableItem p.1)])) :=
  nonnegative_primitive.comp (((subtract_primitive.comp boundary_primitive
    (Primrec.const (WindowCode.numeral 2))).pair (Primrec.const (WindowCode.numeral 1))).pair
    (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair
      (TiedLinearCodeProof.variableItem_primitive.comp Primrec.fst)) (Primrec.const [])))
#print axioms lowerBoundaryGuard_primitive

theorem positiveGuard_primitive : Primrec₂ positiveGuard :=
  disjunction_primitive.comp
    (nonnegative_primitive.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.const [])))
    upperBoundaryGuard_primitive
#print axioms positiveGuard_primitive

theorem negativeGuard_primitive : Primrec₂ negativeGuard :=
  conjunction_primitive.comp
    (nonnegative_primitive.comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
      (BlockRowSubstitutionCodeProof.add_primitive.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const (WindowCode.numeral 1)))).pair
      (Primrec.const []))) lowerBoundaryGuard_primitive
#print axioms negativeGuard_primitive

theorem positive_primitive : PrimrecPred (fun z : Int => 0 < z) := by
  apply (Primrec.nat_lt.comp (Primrec.const 0) BlockRowSubstitutionCodeProof.toNat_primitive).of_eq
  intro z
  omega
#print axioms positive_primitive

theorem negative_primitive : PrimrecPred (fun z : Int => z < 0) := by
  apply (positive_primitive.comp IntegerAlgorithms.Proof.negate_primitive).of_eq
  intro z
  omega
#print axioms negative_primitive

theorem linearizeNonnegative_primitive : Primrec₂ linearizeNonnegative :=
  Primrec.ite (positive_primitive.comp headCoefficient_primitive) positiveGuard_primitive
    (Primrec.ite (negative_primitive.comp headCoefficient_primitive) negativeGuard_primitive
      (nonnegative_primitive.comp ((Primrec.fst.comp Primrec.snd).pair remainingOccurrences_primitive)))
#print axioms linearizeNonnegative_primitive

theorem outsideRow_primitive : Primrec₂ outsideRow :=
  Primrec.ite (Primrec.eq.comp headCoefficient_primitive (Primrec.const (0 : Int))) (Primrec.const 0)
    (disjunction_primitive.comp lowerBoundaryGuard_primitive upperBoundaryGuard_primitive)
#print axioms outsideRow_primitive

theorem bandCandidate_primitive : Primrec (fun p : Nat × (RowData × Nat) => bandCandidate p.1 p.2.1 p.2.2) :=
  BlockRowSubstitutionCodeProof.add_primitive.comp
    (subtract_primitive.comp
      (boundary_primitive.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const (WindowCode.numeral 2)))
    (numeral_primitive.comp (Primrec.snd.comp Primrec.snd))
#print axioms bandCandidate_primitive

theorem actualRowPrograms : PlainBlockLinearizationCodeTargets.ActualRowPrograms :=
  ⟨headCoefficient_primitive.to_comp, remainingOccurrences_primitive.to_comp, mass_primitive.to_comp,
    boundary_primitive.to_comp, positiveGuard_primitive.to_comp, negativeGuard_primitive.to_comp,
    linearizeNonnegative_primitive.to_comp, outsideRow_primitive.to_comp, bandCandidate_primitive.to_comp,
    residueRow_primitive.to_comp, residueAtom_primitive.to_comp⟩
#print axioms actualRowPrograms

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
