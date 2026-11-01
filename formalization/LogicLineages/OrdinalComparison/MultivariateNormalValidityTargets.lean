module
public import LogicLineages.OrdinalComparison.MultivariateNormalValidityDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateNormalStorageGrammar : Prop :=
  (∀ A : MultivariateCollectedNF,
    collectedPositiveSupport (multivariateCollectedShadow A)=multivariateCollectedSupport A) ∧
  (∀ (d : Nat) (A : MultivariateCollectedNF),
    MultivariateCollectedValid d A ↔
      CollectedPositiveValid (multivariateCollectedShadow A) ∧ MultivariateVectorFields d A)

def MultivariateCoefficientValidity : Prop :=
  (∀ a b : List Nat, MultivariateCoefficientCanonical a → MultivariateCoefficientCanonical b →
    MultivariateCoefficientCanonical (multivariateCoefficientAdd a b)) ∧
  (∀ (d i : Nat), i<d →
    (multivariateVariableCoefficients i 1).length≤d ∧
      MultivariateCoefficientCanonical (multivariateVariableCoefficients i 1)) ∧
  (∀ a b : List Nat,
    (multivariateCoefficientAdd a b).length=max a.length b.length)

def FullMultivariateNormalFormValidity : Prop :=
  ∀ (d : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    MultivariateCollectedValid d (multivariateCollectedNormalize E) ∧
      multivariateCollectedSupport (multivariateCollectedNormalize E)=multivariatePositiveHasInput E

end LogicLineages.OrdinalComparison.Targets
