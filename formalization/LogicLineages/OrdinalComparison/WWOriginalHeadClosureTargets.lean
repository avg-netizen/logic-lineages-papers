module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

/-! The admissible all-one head extension, not an arbitrary ordinal valuation,
pays the original universal collapse norm condition under X:=One. -/
def OriginalHeadClosureValue : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (ρ : AdmissibleSubstitution Γ)
    (ρ' : AdmissibleSubstitution (σ :: Γ)),
    (∀ j : Fin (σ.level + 1), ρ'.vector .here j = .one) →
    (∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      ρ'.vector (.there x) j = ρ.vector x j) →
    ∀ t : OrdinalExpression (σ :: Γ),
      expressionValue ρ (ordinalHeadClosure t) = expressionValue ρ' t

def OriginalHeadClosureNormPremise : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (f g : OrdinalExpression (σ :: Γ)),
    CollapseNormPremise f g → CollapseNormPremise (ordinalHeadClosure f) (ordinalHeadClosure g)

def OriginalHeadClosureGrade : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → AmbientGrade Γ i (ordinalHeadClosure t)

end LogicLineages.OrdinalComparison.Source.Targets
