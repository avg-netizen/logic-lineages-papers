module
public import LogicLineages.OrdinalComparison.BinaryMatrixDefinitions

@[expose] public section

/-! Exact finite matrix calibration for paper10 lem:matrix and lem:observable,
paper.tex399–451. Source A_d/product and restricted-partition initial-state
calibration remain distinct obligations before thm:observer. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinaryMatrixStep : Prop :=
  ∀ (K : Type u) [Field K], ∀ D : Nat, ∀ A U : Polynomial K,
    U.degree < (D : WithBot Nat) → ∀ b : Bool,
      actualBinaryCoefficientVector D (actualBinaryPolynomialDigit b (U * A)) =
        Matrix.mulVec (actualBinaryTransitionMatrix D A b) (actualBinaryCoefficientVector D U)

def ActualBinaryMatrixWordCalibration : Prop :=
  ∀ (K : Type u) [Field K], ∀ D : Nat, ∀ A U : Polynomial K,
    A.degree ≤ (D : WithBot Nat) → U.degree < (D : WithBot Nat) → ∀ w : List Bool,
      actualBinaryMatrixWord D A w (actualBinaryCoefficientVector D U) =
        actualBinaryCoefficientVector D (actualBinaryPolynomialWord A w U)

def ActualBinaryMatrixWordObservation : Prop :=
  ∀ D : Nat, ∀ hD : 0 < D, ∀ A U : Polynomial (ZMod 2),
    A.coeff 0 = 1 → A.degree ≤ (D : WithBot Nat) → U.degree < (D : WithBot Nat) →
    ∀ w : List Bool,
      actualBinaryMatrixWord D A w (actualBinaryCoefficientVector D U) ⟨0, hD⟩ =
        PowerSeries.coeff (actualBinaryWordValue w) (actualPolynomialSeriesQuotient A U)

def ActualBinaryMatrixBoundedContinuation : Prop :=
  ∀ D : Nat, ∀ hD : 0 < D, ∀ A U V : Polynomial (ZMod 2),
    A.coeff 0 = 1 → A.degree ≤ (D : WithBot Nat) →
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) → U ≠ V →
      ∃ w : List Bool, w.length ≤ Nat.clog 2 D ∧
        actualBinaryMatrixWord D A w (actualBinaryCoefficientVector D U) ⟨0, hD⟩ ≠
          actualBinaryMatrixWord D A w (actualBinaryCoefficientVector D V) ⟨0, hD⟩

end LogicLineages.OrdinalComparison.Targets
