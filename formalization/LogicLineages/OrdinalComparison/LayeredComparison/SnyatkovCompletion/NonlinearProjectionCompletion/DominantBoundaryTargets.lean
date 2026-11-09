module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryTargets
open DominantBoundary

def ActualScaledBoundary : Prop := ∀ (a target n : Nat), 0 < a →
  (target ≤ a * Phi n ↔
    (n = 0 ∧ target ≤ a * Phi 0) ∨ positiveCrossing a target ≤ n)

/-- Every original witness lies in the actual inverse-selected finite band;
no maximum-input premise is imposed on any retained free parameter. -/
def ActualFiniteBand : Prop := ∀ (i a : Nat) (shift : Int) (lower upper : Term),
  0 < a → ∀ ν : Nat → Nat, (region i a shift lower upper).eval ν →
  (center a lower).value ν - 2 ≤ (((ν i : Int) + shift).toNat) ∧
    (((ν i : Int) + shift).toNat) ≤ (center a lower).value ν + 2

def ActualNonlinearProjection : Prop :=
  ∀ (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix),
    0 < a → i ∉ lower.variables → i ∉ upper.variables → ∀ ν : Nat → Nat,
    ((∃ n : Nat, (Matrix.conjunction (region i a shift lower upper) p).eval
        (Function.update ν i n)) ↔ (project i a shift lower upper p).eval ν)

def ExactParameterSupport : Prop :=
  ∀ (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix),
    i ∉ lower.variables → i ∉ upper.variables → ∀ j : Nat,
    j ∈ (project i a shift lower upper p).variables →
      j ≠ i ∧ (j ∈ lower.variables ∨ j ∈ upper.variables ∨ j ∈ p.variables)

def LiteralCodeCalibration : Prop :=
  (∀ (a : Nat) (lower : Term), Code.center a lower.encode = (center a lower).encode) ∧
  (∀ (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix),
    Code.project (i, a, shift, lower.encode, upper.encode, p.encode) =
      (project i a shift lower upper p).encode)

def ActualNumericProgram : Prop := Computable Code.project

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryTargets
