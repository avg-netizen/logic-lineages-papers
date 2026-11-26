module
public import LogicLineages.PermittedControl.StandardDomainCalibrationDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardDomainCalibrationTargets
open OrdinalComparison Source StandardDomainCalibration

def ClosedCalibration : Prop :=
  (∀ t : OriginalDomain.ClosedExpression,
    SelectedSourceDomain.closedValue Phi t=OriginalDomain.closedValue t) ∧
  (∀ (i : Nat) (t : OriginalDomain.ClosedExpression),
    SelectedSourceDomain.ClosedGrade Phi i t ↔ OriginalDomain.ClosedGrade i t)

/-- A genuine onto correspondence, not inclusion in a smaller admitted domain. -/
def DomainCalibration : Prop := ∀ Γ : List Ty,
  ∃ e : SelectedSourceDomain.AdmissibleSubstitution Phi Γ ≃ OriginalDomain.AdmissibleSubstitution Γ,
    ∀ ρ, SameVector ρ (e ρ)

def ExpressionCalibration : Prop := ∀ (Γ : List Ty)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (σ : OriginalDomain.AdmissibleSubstitution Γ), SameVector ρ σ →
  (SelectedSourceDomain.valuation Phi ρ=OriginalDomain.valuation σ) ∧
  (∀ t : OrdinalExpression Γ,
    SelectedSourceDomain.expressionValue Phi ρ t=OriginalDomain.expressionValue σ t)

/-- Universal collapse guard transports both ways over the entire domain. -/
def GradeCalibration : Prop :=
  (∀ (Γ : List Ty) (f g : OrdinalExpression Γ),
    SelectedSourceDomain.CollapseNormPremise Phi f g ↔ OriginalDomain.CollapseNormPremise f g) ∧
  (∀ (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ),
    SelectedSourceDomain.AmbientGrade Phi Γ i t ↔ OriginalDomain.AmbientGrade Γ i t) ∧
  (∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ::Γ)),
    SelectedSourceDomain.HeadGrade Phi Γ σ i t ↔ OriginalDomain.HeadGrade Γ σ i t)

/-- All policies and source types, literal Option semantics including failures;
this does not assert successful assignment, positivity or norm bounds. -/
def AssignmentCalibration : Prop := ∀ (Γ : List Ty)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (σ : OriginalDomain.AdmissibleSubstitution Γ), SameVector ρ σ →
  ∀ (policy : AdmissibleSum.Policy) (τ : Ty) (a : OriginalTerm Γ τ),
  ((AdmissibleAssignment.assignment policy a).map
    (fun v => fun j => SelectedSourceDomain.expressionValue Phi ρ (v j)))=
  ((AdmissibleAssignment.assignment policy a).map
    (fun v => fun j => OriginalDomain.expressionValue σ (v j)))

def StandardDomainCalibration : Prop := ClosedCalibration ∧ DomainCalibration ∧
  ExpressionCalibration ∧ GradeCalibration ∧ AssignmentCalibration
end LogicLineages.PermittedControl.StandardDomainCalibrationTargets
