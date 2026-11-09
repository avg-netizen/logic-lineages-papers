module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumTargets
open BlockRows PlainMaximum

def ExactOriginalHeadDecomposition : Prop := ∀ (r : Row) (i : Nat) (ν : Nat → Nat),
  rowValue r ν = constantValue r ν + headCoefficient i r * (Phi (ν i) : Int) + remainderValue i r ν

/-- This is derived from the ORIGINAL literal coefficient mass and maximum
frame, not supplied as a domination/oracle field of a solver. Parameters are
deliberately excluded from the remainder and remain unrestricted. -/
def ActualOriginalRemainderBound : Prop :=
  ∀ (bound : List Nat) (r : Row) (i : Nat) (ν : Nat → Nat),
    allowed bound r = true → UniqueMaximum bound i ν → cutoff r ≤ ν i →
      2 * (remainderValue i r ν).natAbs < Phi (ν i)

def ActualLowBoundaryGap : Prop := ∀ (a K n : Nat), 0 < a →
  n < DominantBoundary.positiveCrossing a (2 * K) - 2 → 3 * (a * Phi n) < 2 * K
def ActualHighBoundaryGap : Prop := ∀ (a K n : Nat), 0 < a →
  DominantBoundary.positiveCrossing a (2 * K) + 2 < n → 2 * K < a * Phi n

/-- The actual per-row nonlinear-to-linear clause under one computable source
case. Rows with coefficient zero are retained as their own exact remainder. -/
def ActualNonnegativeLinearization : Prop :=
  ∀ (bound : List Nat) (r : Row) (i : Nat) (ν : Nat → Nat),
    allowed bound r = true → (∀ j ∈ bound, j ∉ r.parameters) →
      UniqueMaximum bound i ν → cutoff r ≤ ν i → OutsideBoundary i r ν →
        ((linearizeNonnegative i r).eval ν ↔ 0 ≤ rowValue r ν)

def ExactEliminandLinearity : Prop := ∀ (bound : List Nat) (r : Row) (i : Nat),
  allowed bound r = true → i ∉ r.parameters → linearIn i (linearizeNonnegative i r) = true
def WholeBlockParameterPreservation : Prop :=
  ∀ (bound : List Nat) (r : Row) (i : Nat),
    (∀ j ∈ bound, j ∉ r.parameters) → ParametersIndependent bound (linearizeNonnegative i r)
def OriginalNameSupport : Prop := ∀ (r : Row) (i j : Nat),
  j ∈ (linearizeNonnegative i r).variables → j ∈ r.variables

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumTargets
