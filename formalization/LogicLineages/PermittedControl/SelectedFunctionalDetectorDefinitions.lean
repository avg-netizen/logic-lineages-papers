module
public import LogicLineages.PermittedControl.SelectedHardnessDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain
open Source.FunctionalDetector (unary alignedLeft alignedRight left right)

/-- Literal positive numeral, not a semantic witness chosen from an oracle. -/
def positiveGrade (ctrl : Nat → Nat) : (n : Nat) →
    ClosedGrade ctrl 0 (UnitObservation.positive n)
  | 0 => .one 0
  | n+1 => .add (positiveGrade ctrl n) (.one 0)

def groundExtension {Γ} (ctrl : Nat → Nat) (ρ : AdmissibleSubstitution ctrl Γ) (n : Nat) :
    AdmissibleSubstitution ctrl (.ground::Γ) where
  vector := fun {_} x j => match x with
    | .here => UnitObservation.positive n
    | .there y => ρ.vector y j
  graded := by
    intro σ x j
    cases x with
    | here =>
      have hj : j=0 := Fin.eq_zero j
      subst j
      exact positiveGrade ctrl n
    | there y => exact ρ.graded y j
  bounded := by
    intro σ x j
    cases x with
    | here => exact le_rfl
    | there y => exact ρ.bounded y j

def extend {Γ} (ctrl : Nat → Nat) (ρ : AdmissibleSubstitution ctrl Γ) (z w : Nat) :=
  groundExtension ctrl (groundExtension ctrl ρ w) z

noncomputable def groundValue {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (t : OriginalTerm Γ .ground) : Nat :=
  ((AdmissibleAssignment.assignment p t).map
    (fun v => finiteValue (expressionValue ctrl ρ (v 0)))).getD 0

def HeadEqual {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) : Prop :=
  ∃ av bv : OrdinalVector Γ 1,
    AdmissibleAssignment.assignment p a=some av ∧
    AdmissibleAssignment.assignment p b=some bv ∧
    expressionValue ctrl ρ (av 1)=expressionValue ctrl ρ (bv 1)
def VectorEqual {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) : Prop :=
  ∃ av bv : OrdinalVector Γ 1,
    AdmissibleAssignment.assignment p a=some av ∧
    AdmissibleAssignment.assignment p b=some bv ∧
    ∀ j : Fin 2, expressionValue ctrl ρ (av j)=expressionValue ctrl ρ (bv j)

def Detects {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) : Prop :=
  let l := groundValue ctrl p ρ (left a b)
  let r := groundValue ctrl p ρ (right a b)
  (∃ lv rv : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment p (left a b)=some lv ∧
    AdmissibleAssignment.assignment p (right a b)=some rv ∧
    expressionValue ctrl ρ (lv 0)=(l : Ordinal) ∧
    expressionValue ctrl ρ (rv 0)=(r : Ordinal)) ∧
  r ≤ l ∧ (l=r ↔ VectorEqual ctrl p ρ a b) ∧
    (¬VectorEqual ctrl p ρ a b → r+2 ≤ l)
end LogicLineages.PermittedControl.SelectedFunctionalDetector
