module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.CodeCalibrationProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmGuardProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.CodePrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open LayeredComparison.SnyatkovCompletion
open RankedWordDecisionCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem negateRow_primitive : Primrec negateRow := by
  let Item := Int × Token
  have hitem : Primrec (fun p : Row × Item => (-p.2.1,p.2.2)) :=
    (LayeredComparison.IntegerAlgorithms.Proof.negate_primitive.comp
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  exact (LayeredComparison.IntegerAlgorithms.Proof.negate_primitive.comp Primrec.fst).pair
    (Primrec.list_map Primrec.snd hitem.to₂)

theorem positiveRow_primitive : Primrec positiveRow :=
  (Primrec.const (-1 : Int)).pair (Primrec.list_cons.comp
    ((Primrec.const (1 : Int)).pair (Primrec.id.pair (Primrec.const ([] : Word))))
    (Primrec.const []))

theorem nonnegative_primitive : Primrec Code.nonnegative :=
  AlgorithmPrograms.nonnegative_encode_primitive

theorem negative_primitive : Primrec Code.negative :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 3)

theorem disjunction_primitive : Primrec₂ Code.disjunction :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 5)

theorem rowEquation_primitive : Primrec Code.rowEquation :=
  AlgorithmPrograms.conjunction_encode_primitive.comp nonnegative_primitive
    (nonnegative_primitive.comp negateRow_primitive)

theorem positiveFrame_primitive : Primrec Code.positiveFrame := by
  have hi : Primrec (fun p : Nat × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Nat × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.list_range (Primrec.const 0)
    (AlgorithmPrograms.conjunction_encode_primitive.comp
      (nonnegative_primitive.comp (positiveRow_primitive.comp hi)) hs).to₂

theorem rowEquations_primitive : Primrec Code.rowEquations := by
  have hr : Primrec (fun p : List Row × (Row × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : List Row × (Row × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (AlgorithmPrograms.conjunction_encode_primitive.comp (rowEquation_primitive.comp hr) hs).to₂

theorem badSign_primitive : Primrec₂ Code.badSign :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (negative_primitive.comp (nonnegative_primitive.comp (negateRow_primitive.comp Primrec.snd)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (nonnegative_primitive.comp Primrec.snd)
      (negative_primitive.comp (rowEquation_primitive.comp Primrec.snd)))

theorem failedPositive_primitive : Primrec Code.failedPositive :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)

/-- Degree, arity, rows, mode and flag are all actual package input data. -/
theorem actualMatrixProgram : Targets.ActualMatrixProgram := by
  have hn : Primrec (fun p : Pair.Package => p.1.2) := Primrec.snd.comp Primrec.fst
  have hr : Primrec (fun p : Pair.Package => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Pair.Package => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec (fun p : Pair.Package => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hf : Primrec (fun p : Pair.Package => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact AlgorithmPrograms.conjunction_encode_primitive.comp (positiveFrame_primitive.comp hn)
    (AlgorithmPrograms.conjunction_encode_primitive.comp (rowEquations_primitive.comp hr)
      (disjunction_primitive.comp (failedPositive_primitive.comp hf) (badSign_primitive.comp hm hc)))

#print axioms negateRow_primitive
#print axioms positiveRow_primitive
#print axioms nonnegative_primitive
#print axioms negative_primitive
#print axioms disjunction_primitive
#print axioms rowEquation_primitive
#print axioms positiveFrame_primitive
#print axioms rowEquations_primitive
#print axioms badSign_primitive
#print axioms failedPositive_primitive
#print axioms actualMatrixProgram

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.CodePrograms
