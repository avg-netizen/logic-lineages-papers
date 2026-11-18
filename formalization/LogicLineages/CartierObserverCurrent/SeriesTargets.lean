module
public import LogicLineages.CartierObserverCurrent.SeriesDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Series.Targets

def SquareCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ F : PowerSeries K, ∀ n : Nat,
      PowerSeries.coeff n (F ^ 2) =
        if 2 ∣ n then (PowerSeries.coeff (n / 2) F) ^ 2 else 0

def SquareDecomposition : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ F : PowerSeries K,
    F = (squareRootDigit false F) ^ 2 +
      PowerSeries.X * (squareRootDigit true F) ^ 2

def SquareUniqueness : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ A B C D : PowerSeries K,
    A ^ 2 + PowerSeries.X * B ^ 2 = C ^ 2 + PowerSeries.X * D ^ 2 → A = C ∧ B = D

def CartierCharacterization : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ A B : PowerSeries K,
    differentialCartier (A ^ 2 + PowerSeries.X * B ^ 2) = B

def CartierCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ F : PowerSeries K, ∀ n : Nat,
      PowerSeries.coeff n (differentialCartier F) =
        (frobeniusEquiv K 2).symm (PowerSeries.coeff (2 * n + 1) F)
end LogicLineages.CartierObserverCurrent.Series.Targets
