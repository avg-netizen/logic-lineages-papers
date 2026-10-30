module
public import LogicLineages.OrdinalComparison.BinaryPolynomialWordDefinitions

@[expose] public section

/-! External continuation, 30 October 2026. Literal finite polynomial-word
bridge for paper10 lem:observable (paper.tex437–451), building on lem:matrix's
actual quotient update. The matrix representation and restricted-partition
initial-state calibration are separate obligations. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinaryPolynomialWordQuotient : Prop :=
  ∀ A U : Polynomial (ZMod 2), A.coeff 0 = 1 → ∀ w : List Bool,
    actualBinarySeriesWord w (actualPolynomialSeriesQuotient A U) =
      actualPolynomialSeriesQuotient A (actualBinaryPolynomialWord A w U)

def ActualBinaryPolynomialWordDegree : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, ∀ D : Nat,
    A.degree ≤ (D : WithBot Nat) → U.degree < (D : WithBot Nat) → ∀ w : List Bool,
      (actualBinaryPolynomialWord A w U).degree < (D : WithBot Nat)

/-- The actual final numerator coordinate reads the selected original series
coefficient, including the empty continuation and the zero numerator. -/
def ActualBinaryPolynomialWordObservation : Prop :=
  ∀ A U : Polynomial (ZMod 2), A.coeff 0 = 1 → ∀ w : List Bool,
    (actualBinaryPolynomialWord A w U).coeff 0 =
      PowerSeries.coeff (actualBinaryWordValue w) (actualPolynomialSeriesQuotient A U)

def ActualBinaryPolynomialBoundedContinuation : Prop :=
  ∀ A U V : Polynomial (ZMod 2), A.coeff 0 = 1 → ∀ D : Nat,
    A.degree ≤ (D : WithBot Nat) →
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) → U ≠ V →
      ∃ w : List Bool, w.length ≤ Nat.clog 2 D ∧
        (actualBinaryPolynomialWord A w U).coeff 0 ≠
          (actualBinaryPolynomialWord A w V).coeff 0

end LogicLineages.OrdinalComparison.Targets
