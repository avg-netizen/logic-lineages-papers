module
public import LogicLineages.OrdinalComparison.SingleCoreEvaluationDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualSingleCoreGroundCode : Prop := ∀ (E : MultivariatePositiveExpr) (xs : List Nat),
  Source.ForwardTranslation.instantiateScalarCode xs (multivariatePositiveEncode E)=
    positiveExprEncode (singleCoreGround xs E)

def ActualSingleCoreGroundValue : Prop := ∀ (E : MultivariatePositiveExpr) (xs : List Nat),
  actualFixedLimitProfileEval (singleCoreGround xs E) 0=
    actualMultivariatePositiveEval E (fun i => xs.getD i 0+1)

/-- Actual whole arbitrary nested positive-core finite evaluation. Existing
source Scalar's restricted origin of heads is NOT imposed as a new premise. -/
def FullActualSingleCoreEvaluation : Prop := Computable₂ encodedSingleCoreEvaluation ∧
  ActualSingleCoreGroundCode ∧ ActualSingleCoreGroundValue ∧
  ∀ (E : MultivariatePositiveExpr) (xs : List Nat),
    encodedSingleCoreEvaluation (multivariatePositiveEncode E) xs=
      actualMultivariatePositiveEval E (fun i => xs.getD i 0+1)

end LogicLineages.OrdinalComparison.Targets
