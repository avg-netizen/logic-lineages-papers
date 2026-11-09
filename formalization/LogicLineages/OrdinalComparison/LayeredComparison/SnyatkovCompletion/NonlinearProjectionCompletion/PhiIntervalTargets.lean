module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalTargets
open PhiInterval

def ActualLowerBoundary : Prop := ∀ (a : Nat) (shift : Int) (target n : Nat), 0 < a →
  ((0 ≤ (n : Int) + shift ∧ target ≤ a * Phi (((n : Int) + shift).toNat)) ↔
    lowerBound a shift target ≤ n)

def ActualResidueRepresentative : Prop := ∀ (m start residue n : Nat), 0 < m →
  start ≤ n → n % m = residue % m →
    ∃ d : Nat, d < m ∧ start + d ≤ n ∧ (start + d) % m = residue % m

/-- A genuine uniform nonlinear projection, with arbitrary retained symbolic
endpoints and residue. No no-wide, maximal-name or decision-supplier premise. -/
def ActualNonlinearProjection : Prop :=
  ∀ (i a : Nat) (shift : Int) (m : Nat) (lower upper residue : Term),
    0 < a → 0 < m → i ∉ lower.variables → i ∉ upper.variables → i ∉ residue.variables →
    ∀ ν : Nat → Nat,
    ((∃ n : Nat, (interval i a shift m lower upper residue).eval (Function.update ν i n)) ↔
      (project i a shift m lower upper residue).eval ν)

def ExactParameterSupport : Prop :=
  ∀ (i a : Nat) (shift : Int) (m : Nat) (lower upper residue : Term),
    i ∉ lower.variables → i ∉ upper.variables → i ∉ residue.variables → ∀ j : Nat,
    j ∈ (project i a shift m lower upper residue).variables →
      j ≠ i ∧ (j ∈ lower.variables ∨ j ∈ upper.variables ∨ j ∈ residue.variables)

def LiteralCodeCalibration : Prop :=
  ∀ (i a : Nat) (shift : Int) (m : Nat) (lower upper residue : Term),
    Code.project (i, a, shift, m, lower.encode, upper.encode, residue.encode) =
      (project i a shift m lower upper residue).encode

def ActualNumericProgram : Prop := Computable Code.project

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalTargets
