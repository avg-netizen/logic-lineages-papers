module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

def OriginalFiniteValueCalibration : Prop :=
  ∀ n : Nat, finiteValue (n : Ordinal) = n

/-- Scalar B-expressions have genuine finite ordinal values, justifying the
natural-number interpretation in the source F2 premise. -/
def OriginalClosedScalarFinite : Prop :=
  ∀ t : ClosedExpression, ClosedGrade 0 t → ∃ n : Nat, closedValue t = (n : Ordinal)

def OriginalAmbientScalarFinite : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ), AmbientGrade Γ 0 t →
    ∀ ρ : AdmissibleSubstitution Γ, ∃ n : Nat, expressionValue ρ t = (n : Ordinal)

def OriginalAllOneSubstitution : Prop :=
  ∀ Γ : List Ty, ∃ ρ : AdmissibleSubstitution Γ,
    ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)), ρ.vector x j = .one

def OriginalHeadOneExtension : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (ρ : AdmissibleSubstitution Γ),
    ∃ ρ' : AdmissibleSubstitution (σ :: Γ),
      (∀ j : Fin (σ.level + 1), ρ'.vector .here j = .one) ∧
      (∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
        ρ'.vector (.there x) j = ρ.vector x j)

def OriginalHeadAmbientInclusion : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → AmbientGrade (σ :: Γ) i t

def OriginalHeadLiteralAdmission : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → LiteralPartialDomain.Domain Γ σ i t

end LogicLineages.OrdinalComparison.Source.Targets
