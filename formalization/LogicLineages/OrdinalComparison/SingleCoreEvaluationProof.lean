module
public import LogicLineages.OrdinalComparison.SingleCoreEvaluationTargets
public import LogicLineages.OrdinalComparison.WWEncodedScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreEvaluation
open Source.ForwardTranslation

private theorem instantiate_constant (xs : List Nat) (n : Nat) :
    instantiateScalarCode xs (4*n)=4*n := by
  rw [instantiateScalarCode]
  simp

private theorem instantiate_variable (xs : List Nat) (n : Nat) :
    instantiateScalarCode xs (4*n+1)=4*(xs.getD n 0+1) := by
  have hm : (4*n+1)%4=1 := by omega
  have hd : (4*n+1)/4=n := by omega
  rw [instantiateScalarCode]
  simp [hm,hd]

private theorem instantiate_add (xs : List Nat) (a b : Nat) :
    instantiateScalarCode xs (4*Nat.pair a b+2)=
      4*Nat.pair (instantiateScalarCode xs a) (instantiateScalarCode xs b)+2 := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [instantiateScalarCode]
  simp [hm,hd]

private theorem instantiate_head (xs : List Nat) (rho a : Nat) :
    instantiateScalarCode xs (4*Nat.pair rho a+3)=
      4*Nat.pair rho (instantiateScalarCode xs a)+3 := by
  have hm : (4*Nat.pair rho a+3)%4=3 := by omega
  have hd : (4*Nat.pair rho a+3)/4=Nat.pair rho a := by omega
  rw [instantiateScalarCode]
  simp [hm,hd]

theorem source_code : Targets.ActualSingleCoreGroundCode := by
  intro E xs
  induction E with
  | constant c => exact instantiate_constant xs c
  | input i => exact instantiate_variable xs i
  | add E F ihE ihF =>
    simp only [multivariatePositiveEncode,singleCoreGround,positiveExprEncode,instantiate_add,ihE,ihF]
  | head rho E ih =>
    simp only [multivariatePositiveEncode,singleCoreGround,positiveExprEncode,instantiate_head,ih]

theorem source_value : Targets.ActualSingleCoreGroundValue := by
  intro E xs
  induction E with
  | constant c => rfl
  | input i => rfl
  | add E F ihE ihF => exact congrArg₂ (·+·) ihE ihF
  | head rho E ih => exact congrArg (actualProfileHead rho) ih

theorem program : Computable₂ encodedSingleCoreEvaluation := encodedScalarComputable

theorem actual_value (E : MultivariatePositiveExpr) (xs : List Nat) :
    encodedSingleCoreEvaluation (multivariatePositiveEncode E) xs=
      actualMultivariatePositiveEval E (fun i => xs.getD i 0+1) := by
  unfold encodedSingleCoreEvaluation encodedScalarValue
  rw [source_code E xs,encodedPositiveFoldSourceCorrect (singleCoreGround xs E),source_value E xs]

theorem full : Targets.FullActualSingleCoreEvaluation := ⟨program,source_code,source_value,actual_value⟩

end LogicLineages.OrdinalComparison.SingleCoreEvaluation
