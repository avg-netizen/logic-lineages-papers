module
public import LogicLineages.OrdinalComparison.SeriesContinuationDefinitions
public import LogicLineages.OrdinalComparison.SeriesObservabilityTargets

@[expose] public section

/-! Literal binary SERIES-continuation suppliers for source10 lem:observable.
This fixes the actual Lambda_b coefficient selectors and actual Nat.bits
continuations. The finite polynomial/matrix transition calibration of the
original observer is NOT supplied as a premise and remains a separate pending
source obligation; these suppliers alone earn no numbered completion. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinarySeriesWordSelection : Prop :=
  ∀ (K : Type u) [Field K], ∀ w : List Bool, ∀ F : PowerSeries K,
    PowerSeries.coeff 0 (actualBinarySeriesWord w F) = PowerSeries.coeff (actualBinaryWordValue w) F

def ActualBinaryDigitsValueAndBound : Prop :=
  ∀ D k : Nat, k < D → (Nat.bits k).length ≤ Nat.clog 2 D ∧ actualBinaryWordValue (Nat.bits k) = k

def ActualSeriesBoundedContinuation : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U V : Polynomial K, A.coeff 0 = 1 → ∀ D : Nat,
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) → U ≠ V →
      ∃ w : List Bool, w.length ≤ Nat.clog 2 D ∧
        PowerSeries.coeff 0 (actualBinarySeriesWord w (actualPolynomialSeriesQuotient A U)) ≠
          PowerSeries.coeff 0 (actualBinarySeriesWord w (actualPolynomialSeriesQuotient A V))

end LogicLineages.OrdinalComparison.Targets
