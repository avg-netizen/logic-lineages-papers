module
public import LogicLineages.OrdinalComparison.SeriesObservabilityTargets
public import LogicLineages.OrdinalComparison.BinaryMatrixTargets
public import LogicLineages.OrdinalComparison.BinaryPolynomialWordTargets

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FullObservability.Targets
open LogicLineages.OrdinalComparison

/-- Arbitrary field, genuine expansion; the stronger all-cutoff version includes
source degree A = D and retains the zero-dimensional case. -/
def InitialCoefficients : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U V : Polynomial K, A.coeff 0 = 1 → ∀ D : Nat,
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) →
    (∀ n : Nat, n < D → PowerSeries.coeff n (actualPolynomialSeriesQuotient A U) =
      PowerSeries.coeff n (actualPolynomialSeriesQuotient A V)) → U = V

/-- Actual numerator outputs, including D=0 vacuity and empty word at index0. -/
def PolynomialContinuation : Prop :=
  ∀ A U V : Polynomial (ZMod 2), A.coeff 0 = 1 → ∀ D : Nat,
    A.degree ≤ (D : WithBot Nat) →
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) → U ≠ V →
      ∃ w : List Bool, w.length ≤ Nat.clog 2 D ∧
        (actualBinaryPolynomialWord A w U).coeff 0 ≠
          (actualBinaryPolynomialWord A w V).coeff 0

/-- Literal finite matrix observer, not Boolean reachability. -/
def MatrixContinuation : Prop :=
  ∀ D : Nat, ∀ hD : 0 < D, ∀ A U V : Polynomial (ZMod 2),
    A.coeff 0 = 1 → A.degree ≤ (D : WithBot Nat) →
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) → U ≠ V →
      ∃ w : List Bool, w.length ≤ Nat.clog 2 D ∧
        actualBinaryMatrixWord D A w (actualBinaryCoefficientVector D U) ⟨0, hD⟩ ≠
          actualBinaryMatrixWord D A w (actualBinaryCoefficientVector D V) ⟨0, hD⟩

def CompleteObservability : Prop :=
  InitialCoefficients.{u} ∧ PolynomialContinuation ∧ MatrixContinuation
end LogicLineages.CartierObserverCurrent.FullObservability.Targets
