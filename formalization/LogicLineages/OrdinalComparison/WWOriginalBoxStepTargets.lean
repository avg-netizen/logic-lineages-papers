module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

/-- Original Proposition 2.2's actual natural-product upper norm estimate. -/
def ActualNaturalProductUpperNorm : Prop :=
  ∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm (ordinalNaturalProduct a b) ≤ actualOrdinalNorm a * actualOrdinalNorm b

/-- The literal positive box step uses genuine ordinal exponentiation and
natural product, under actual admissible original substitutions. No output
norm estimate is assumed. -/
def OriginalBoxStepNorm : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (h f g : OrdinalExpression Γ),
    actualOrdinalNorm (expressionValue ρ (.emul h (.add f g))) ≤
      2 ^ actualOrdinalNorm (expressionValue ρ h) *
        (actualOrdinalNorm (expressionValue ρ f) + actualOrdinalNorm (expressionValue ρ g))

end LogicLineages.OrdinalComparison.Source.Targets
