module
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.FieldTheory.Perfect

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Series

/-- Actual arbitrary formal series selector with inverse Frobenius on coefficients. -/
noncomputable def squareRootDigit {K : Type u} [Field K] [CharP K 2] [PerfectRing K 2]
    (b : Bool) (F : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => (frobeniusEquiv K 2).symm (PowerSeries.coeff (Nat.bit b n) F)

noncomputable def differentialCartier {K : Type u} [Field K] [CharP K 2] [PerfectRing K 2]
    (F : PowerSeries K) : PowerSeries K := squareRootDigit true F
end LogicLineages.CartierObserverCurrent.Series
