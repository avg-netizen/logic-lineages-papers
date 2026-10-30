module
public import LogicLineages.OrdinalComparison.SeriesObservabilityDefinitions

@[expose] public section

/-! Exact algebraic clause of source paper10 lem:observable, paper.tex437–451:
first D coefficients of the actual formal expansion U/A determine every
numerator of degree<D when A(0)=1. We prove the stronger all-cutoff statement;
the later binary-continuation length clause is a SEPARATE pending target.
No polynomial/series equation or inverse identity is assumed as a supplier. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualSeriesQuotientIdentity : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, A.coeff 0 = 1 →
    (A : PowerSeries K) * actualPolynomialSeriesQuotient A U = (U : PowerSeries K)

def ActualInitialSeriesCoefficientReconstruction : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U V : Polynomial K, A.coeff 0 = 1 → ∀ D : Nat,
    (∀ n : Nat, n < D → PowerSeries.coeff n (actualPolynomialSeriesQuotient A U) =
      PowerSeries.coeff n (actualPolynomialSeriesQuotient A V)) →
    ∀ n : Nat, n < D → U.coeff n = V.coeff n

def ActualPolynomialNumeratorObservability : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U V : Polynomial K, A.coeff 0 = 1 → ∀ D : Nat,
    U.degree < (D : WithBot Nat) → V.degree < (D : WithBot Nat) →
    (∀ n : Nat, n < D → PowerSeries.coeff n (actualPolynomialSeriesQuotient A U) =
      PowerSeries.coeff n (actualPolynomialSeriesQuotient A V)) → U = V

end LogicLineages.OrdinalComparison.Targets
