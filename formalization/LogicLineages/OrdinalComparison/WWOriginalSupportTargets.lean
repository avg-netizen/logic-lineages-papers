module
public import LogicLineages.OrdinalComparison.WWOriginalSupportDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

def OriginalSupportedExtension : Prop :=
  ∀ (Γ : List Ty) (S : VariableName Γ → Prop) (ρ : SupportedSubstitution Γ S),
    ∃ ρ' : AdmissibleSubstitution Γ, ∀ c, valuation ρ' c = supportedValuation ρ c

def OriginalComparisonSupportCoverage : Prop :=
  ∀ (Γ : List Ty) (t u : OrdinalExpression Γ),
    UsesOnly (comparisonSupport t u) t ∧ UsesOnly (comparisonSupport t u) u

/-- Exact support/context equivalence for arbitrary comparisons, including the
source norm and F2 predicates. No condition is added to the comparison itself. -/
def OriginalSupportComparisonBridge : Prop :=
  ∀ (Γ : List Ty) (S : VariableName Γ → Prop) (t u : OrdinalExpression Γ),
    UsesOnly S t → UsesOnly S u → ∀ P : Ordinal.{0} → Ordinal.{0} → Prop,
    (∀ ρ : AdmissibleSubstitution Γ, P (expressionValue ρ t) (expressionValue ρ u)) ↔
    (∀ ρ : SupportedSubstitution Γ S, P (supportedValue ρ t) (supportedValue ρ u))

/-- Source-facing non-strict scalar clause, under exactly the occurring-vector
substitutions of original Definition 2.7. The assembled-domain and bounded-norm
claims are deliberately not part of this standalone adapter. -/
def OriginalSourceWeakScalar : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ 0 t → ∃ v : OrdinalPartialVector Γ σ,
      AdmissiblePartial.run p 0 t = some v ∧
      ∀ ρ : SupportedSubstitution Γ (comparisonSupport (ordinalHeadClosure t) (v 0)),
        supportedValue ρ (ordinalHeadClosure t) ≤ supportedValue ρ (v 0)

end LogicLineages.OrdinalComparison.Source.Targets
