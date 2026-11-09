module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearTargets
open BlockRows TiedLinear

def LiteralTokenRoundTrip : Prop := ∀ (table : List Token) (x : Nat) (t : Token),
  t ∈ table → tokenOfName table x (tokenName table x t) = t

/-- Original Boolean positions include any explicit original domain guards.
The sole quantified value is the selected ORIGINAL natural variable. -/
def ActualTiedLinearElimination : Prop := ∀ (x : Nat) (p : Formula),
  PlainMaximum.linearIn x p = true → ∀ ν : Nat → Nat,
    ((eliminate x p).eval ν ↔ ∃ n : Nat, p.eval (Function.update ν x n))

def ExactOriginalNameSupport : Prop := ∀ (x : Nat) (p : Formula),
  PlainMaximum.linearIn x p = true → ∀ j : Nat,
    (j ∈ (eliminate x p).variables ↔ j ≠ x ∧ j ∈ p.variables)

/-- Only original parameter tokens enter constants. Other bound names' Phi
occurrences remain literal occurrences rather than being frozen as parameters. -/
def WholeBlockParameterIndependence : Prop :=
  ∀ (bound : List Nat) (x : Nat) (p : Formula),
    ParametersIndependent bound p → ParametersIndependent bound (eliminate x p)

def RemainingPlainClass : Prop := ∀ (bound : List Nat) (x : Nat) (p : Formula),
  allowed bound p = true → PlainMaximum.linearIn x p = true →
    allowed (bound.erase x) (eliminate x p) = true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearTargets
