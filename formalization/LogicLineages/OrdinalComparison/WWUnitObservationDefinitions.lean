module
public import LogicLineages.OrdinalComparison.SourceOneUnitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitObservation
open OriginalDomain

/-- A literal finite closed Add/One tree with positive natural value n+1. -/
def positive : Nat → ClosedExpression
  | 0 => .one
  | n+1 => .add (positive n) .one

def positiveGrade : (n : Nat) → ClosedGrade 0 (positive n)
  | 0 => .one 0
  | n+1 => .add (positiveGrade n) (.one 0)

def vector {Γ : List Ty} (ρ : Variable Γ .ground → Nat) :
    {σ : Ty} → Variable Γ σ → Fin (σ.level+1) → ClosedExpression
  | .ground, x, _ => positive (ρ x)
  | .arrow _ _, _, _ => .one

/-- A genuine original-domain admissible vector substitution: ground values
are arbitrary positive finite inputs; every coordinate of a functional name
is literal one. This is an observation, not a claimed source inhabitant. -/
def substitution {Γ : List Ty} (ρ : Variable Γ .ground → Nat) : AdmissibleSubstitution Γ where
  vector := vector ρ
  graded := by
    intro σ x j
    cases σ with
    | ground =>
        have hj : j=0 := Fin.eq_zero j
        subst j
        exact positiveGrade (ρ x)
    | arrow a b => exact .one j.val
  bounded := by
    intro σ x j
    cases σ <;> exact le_rfl

/-- Delete only the selected functional occurrence. Ground inputs are pulled
back through the actual inverse permutation, so all other names stay shared. -/
def remainingInputs (left right : List Ty) (σ : Ty)
    (ρ : Variable (left ++ σ :: right) .ground → Nat) :
    Variable (left ++ right) .ground → Nat :=
  fun x => ρ (SelectedBinder.moveFromHead left right σ (.there x))
end LogicLineages.OrdinalComparison.Source.UnitObservation
