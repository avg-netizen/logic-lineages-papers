module
public import LogicLineages.OrdinalComparison.LinkedResidueDefinitions
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Full literal source paper10 lem:bounds (paper.tex568–591). The middle
comparison uses an ordinary real quotient and the last comparison uses the
actual real exponent 2r/3; neither is silently replaced by natural truncation.
Source u=Phi(v) with a genuine Theta entry lies in the stronger u>=4 domain. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualRealExponentialRootGap : Prop :=
  ∀ r Delta : Nat, 96 ≤ r → Delta < r →
    Real.rpow 2 (2 * (r : Real) / 3) * (Delta : Real) <
      (2 : Real) ^ r / ((r : Real) + 1)

def FullActualLinkedResidueBounds : Prop :=
  ∀ u : Nat, 4 ≤ u →
    96 ≤ actualLinkedHalfExponent u ∧
    actualLinkedDegree u < actualLinkedHalfExponent u ∧
    0 < actualLinkedDegree u - 2 * actualLinkedOffset u ∧
    actualLinkedDegree u - 2 * actualLinkedOffset u < actualLinkedModulus u ∧
    (2 : Real) ^ actualLinkedHalfExponent u / ((actualLinkedHalfExponent u : Real) + 1) <
      (Nat.totient (actualLinkedModulus u) : Real) ∧
    Real.rpow 2 (2 * (actualLinkedHalfExponent u : Real) / 3) * (actualLinkedDegree u : Real) <
      (2 : Real) ^ actualLinkedHalfExponent u / ((actualLinkedHalfExponent u : Real) + 1)

end LogicLineages.OrdinalComparison.Targets
