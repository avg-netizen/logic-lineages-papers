module
public import LogicLineages.OrdinalComparison.PolynomialDigitDefinitions

@[expose] public section

/-! Actual finite-polynomial transition suppliers for paper10 lem:matrix and
lem:observable: exact coefficient selector, formal-series embedding and proper
numerator closure. The characteristic-two denominator/quotient transport is
still a separate pending mathematical obligation, never an assumed field. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinaryPolynomialDigitCoefficient : Prop :=
  ∀ (K : Type u) [Field K], ∀ b : Bool, ∀ P : Polynomial K, ∀ n : Nat,
    (actualBinaryPolynomialDigit b P).coeff n = P.coeff (Nat.bit b n)

def ActualBinaryPolynomialDigitSeries : Prop :=
  ∀ (K : Type u) [Field K], ∀ b : Bool, ∀ P : Polynomial K,
    (actualBinaryPolynomialDigit b P : PowerSeries K) = actualBinarySeriesDigit b (P : PowerSeries K)

def ActualBinaryPolynomialStepDegree : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, ∀ D : Nat,
    A.degree ≤ (D : WithBot Nat) → U.degree < (D : WithBot Nat) → ∀ b : Bool,
      (actualBinaryPolynomialDigit b (U * A)).degree < (D : WithBot Nat)

end LogicLineages.OrdinalComparison.Targets
