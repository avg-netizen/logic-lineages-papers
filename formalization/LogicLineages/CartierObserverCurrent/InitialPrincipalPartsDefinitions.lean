module
public import LogicLineages.CartierObserverCurrent.RationalCoverageDefinitions
public import Mathlib.Algebra.Polynomial.PartialFractions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.InitialPrincipalParts
open SplittingRoots RootInterpolation

/-- All initial principal coefficients through the uniform true source budget. -/
def Coefficients (d M : Nat) := Root d → Fin M → FieldAt d

/-- Actual higher-pole rational sum; index j means pole order j+1. -/
noncomputable def reconstruct (d M : Nat) (b : Coefficients d M) : RatFunc (FieldAt d) := by
  classical
  letI : Fintype (Root d) := by unfold Root; infer_instance
  exact ∑ z : Root d, ∑ j : Fin M,
    Basic.rationalC (b z j) / (Basic.rationalX - Basic.rationalC z.val) ^ (j.val + 1)

/-- Independent proper rational state with actual canonical denominator bound. -/
noncomputable def bounded (d M : Nat) (f : RatFunc (FieldAt d)) : Prop :=
  MixedProper.proper f ∧ f.denom ∣ (rootProduct d) ^ M

/-- Actual initial mapped source fraction, not a supplied partial-fraction expansion. -/
noncomputable def source (d : Nat) (P : Polynomial (ZMod 2)) : RatFunc (FieldAt d) :=
  algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d))
      (P.map (algebraMap (ZMod 2) (FieldAt d))) /
    algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (splitPolynomial d)
end LogicLineages.CartierObserverCurrent.InitialPrincipalParts
