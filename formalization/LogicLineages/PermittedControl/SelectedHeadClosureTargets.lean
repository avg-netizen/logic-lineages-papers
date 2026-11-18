module
public import LogicLineages.PermittedControl.SelectedSourceDomainDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHeadClosureTargets
open OrdinalComparison Source SelectedSourceDomain

/-! The admissible all-one head extension, not an arbitrary ordinal valuation,
pays the original universal collapse norm condition under X:=One. -/
def HeadClosureValue : Prop :=
  ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (ρ' : AdmissibleSubstitution ctrl (σ :: Γ)),
    (∀ j : Fin (σ.level + 1), ρ'.vector .here j = .one) →
    (∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      ρ'.vector (.there x) j = ρ.vector x j) →
    ∀ t : OrdinalExpression (σ :: Γ),
      expressionValue ctrl ρ (ordinalHeadClosure t) = expressionValue ctrl ρ' t

def HeadClosureNormPremise : Prop :=
  ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (f g : OrdinalExpression (σ :: Γ)),
    CollapseNormPremise ctrl f g → CollapseNormPremise ctrl (ordinalHeadClosure f) (ordinalHeadClosure g)

def HeadClosureGrade : Prop :=
  ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade ctrl Γ σ i t → AmbientGrade ctrl Γ i (ordinalHeadClosure t)

def HeadOneExtension : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (ρ : AdmissibleSubstitution ctrl Γ), ∃ ρ' : AdmissibleSubstitution ctrl (σ :: Γ),
    (∀ j : Fin (σ.level + 1), ρ'.vector .here j = .one) ∧
    (∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      ρ'.vector (.there x) j = ρ.vector x j)

def FullSelectedHeadClosure : Prop :=
  HeadOneExtension ∧ HeadClosureValue ∧ HeadClosureNormPremise ∧ HeadClosureGrade

end LogicLineages.PermittedControl.SelectedHeadClosureTargets
