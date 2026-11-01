module
public import LogicLineages.OrdinalComparison.MultivariateNormalizeCodeDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateCoefficientPrograms : Prop :=
  Primrec₂ encodedMultivariateCoefficientAdd ∧ Primrec₂ encodedMultivariateVariableCoefficients ∧
  (∀ a b : List Nat,
    encodedMultivariateCoefficientAdd (multivariateCoefficientCode a) (multivariateCoefficientCode b)=
      multivariateCoefficientCode (multivariateCoefficientAdd a b)) ∧
  (∀ i a : Nat, encodedMultivariateVariableCoefficients i a=
    multivariateCoefficientCode (multivariateVariableCoefficients i a))

def MultivariateCollectedAdditionProgram : Prop :=
  Primrec₂ encodedMultivariateCollectedAdd ∧
  ∀ A B : MultivariateCollectedNF,
    encodedMultivariateCollectedAdd (multivariateCollectedCode A) (multivariateCollectedCode B)=
      multivariateCollectedCode (multivariateCollectedAdd A B)

/-- Actual uniform numeric realization of the cap-INDEPENDENT literal
bottom-up normalizer, not a semantic identity flag or a compiler-image test. -/
def MultivariateCollectedNormalizationProgram : Prop :=
  Computable encodedMultivariateCollectedNormalize ∧
  ∀ E : MultivariatePositiveExpr,
    encodedMultivariateCollectedNormalize (multivariatePositiveEncode E)=
      multivariateCollectedCode (multivariateCollectedNormalize E)

end LogicLineages.OrdinalComparison.Targets
