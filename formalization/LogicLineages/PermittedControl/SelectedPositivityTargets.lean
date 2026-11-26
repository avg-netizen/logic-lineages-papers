module
public import LogicLineages.PermittedControl.SelectedSourceDomainDefinitions
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPositivityTargets
open OrdinalComparison Source SelectedSourceDomain

/-- Closure is syntactic and needs no law on the collapse control. -/
def ValueClosure : Prop :=
  (∀ (f : Nat → Nat) (t : ClosedExpression), closedValue f t < epsilonZero) ∧
  (∀ (f : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution f Γ)
    (t : OrdinalExpression Γ), expressionValue f ρ t < epsilonZero)

/-- Positivity is proved for the actual selected controls, not arbitrary functions. -/
def GradedPositivity : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  (∀ (i : Nat) (t : ClosedExpression), ClosedGrade f i t → 0 < closedValue f t) ∧
  (∀ (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ), AmbientGrade f Γ i t →
    ∀ (ρ : AdmissibleSubstitution f Γ), 0 < expressionValue f ρ t) ∧
  (∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade f Γ σ i t → ∀ (ρ : AdmissibleSubstitution f (σ :: Γ)),
      0 < expressionValue f ρ t)

/-- Genuine positive finite witnesses calibrate the source scalar guard. -/
def PositiveScalars : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  (∀ (t : ClosedExpression), ClosedGrade f 0 t → ∃ n : Nat, 0 < n ∧
    closedValue f t = (n : Ordinal.{0}) ∧ finiteValue (closedValue f t) = n ∧
      actualOrdinalNorm (closedValue f t) = n) ∧
  (∀ (Γ : List Ty) (t : OrdinalExpression Γ), AmbientGrade f Γ 0 t →
    ∀ (ρ : AdmissibleSubstitution f Γ), ∃ n : Nat, 0 < n ∧
      expressionValue f ρ t = (n : Ordinal.{0}) ∧ finiteValue (expressionValue f ρ t) = n ∧
        actualOrdinalNorm (expressionValue f ρ t) = n)

def FullSelectedPositivity : Prop := ValueClosure ∧ GradedPositivity ∧ PositiveScalars

end LogicLineages.PermittedControl.SelectedPositivityTargets
