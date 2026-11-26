module
public import LogicLineages.PermittedControl.SelectedHardnessDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessTargets
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment
open SelectedSourceDomain SelectedHardness

def CoordinateFacts : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary),
  ∃ v : OrdinalVector Γ 1, assignment p a = some v ∧
    expressionValue ctrl ρ (v 0) = (value0 ctrl p ρ a : Ordinal) ∧
    expressionValue ctrl ρ (v 1) = value1 ctrl p ρ a ∧
    0 < value0 ctrl p ρ a ∧ 0 < value1 ctrl p ρ a ∧
    value1 ctrl p ρ a < epsilonZero ∧ actualOrdinalNorm (value1 ctrl p ρ a) ≤ value0 ctrl p ρ a

/-- Actual P/S/H values for arbitrary policy and actual sources; no assignment,
head, norm, scalar or computational oracle premise. -/
def CombinatorValues : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ)
    (a b : OriginalTerm Γ unary),
  value1 ctrl p ρ (identity (Γ := Γ)) = 1 ∧
  value1 ctrl p ρ (project a b) = projectHead (value1 ctrl p ρ a) (value1 ctrl p ρ b) ∧
  value1 ctrl p ρ (combine a b) = combineHead (value1 ctrl p ρ a) (value1 ctrl p ρ b) ∧
  value0 ctrl p ρ (combine a b) = ParametricActualCollapse.collapseWith ctrl
    (ordinalNaturalProduct Ordinal.omega0 (combineHead (value1 ctrl p ρ a) (value1 ctrl p ρ b)) +
      ((9*value0 ctrl p ρ a+5*value0 ctrl p ρ b+13 : Nat) : Ordinal)) ∧
  value1 ctrl p ρ (liftOmega a) = liftHead (value1 ctrl p ρ a)

/-- Exact printed differences live only in the signed Cantor-monomial group. -/
def SignedCombinatorValues : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ)
    (a b : OriginalTerm Γ unary),
  Source.SignedPair.signedCNF (value1 ctrl p ρ (project a b)) =
    (8 : Int) • Source.SignedPair.signedCNF (value1 ctrl p ρ a) +
    (4 : Int) • Source.SignedPair.signedCNF (value1 ctrl p ρ b) +
    (8 : Int) • Source.SignedPair.signedCNF 1 ∧
  Source.SignedPair.signedCNF (value1 ctrl p ρ (combine a b)) =
    (8 : Int) • Source.SignedPair.signedCNF (value1 ctrl p ρ a) +
    (8 : Int) • Source.SignedPair.signedCNF (value1 ctrl p ρ b) +
    (16 : Int) • Source.SignedPair.signedCNF 1 ∧
  Source.SignedPair.signedCNF (value1 ctrl p ρ (liftOmega a)) =
    (2 : Int) • Source.SignedPair.omegaShift (Source.SignedPair.signedCNF (value1 ctrl p ρ a)) +
    (3 : Int) • Source.SignedPair.signedCNF Ordinal.omega0

def SelectedHardnessCombinators : Prop := CoordinateFacts ∧ CombinatorValues ∧ SignedCombinatorValues
end LogicLineages.PermittedControl.SelectedHardnessTargets
