module
public import LogicLineages.CartierObserverCurrent.ThinRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Thin.Targets

def ActualPolynomialSquareRootDigitCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ b : Bool, ∀ P : Polynomial K, ∀ n : Nat,
      ((actualPolynomialSquareRootDigit b P).coeff n) ^ 2 = P.coeff (Nat.bit b n)

def ActualPolynomialSquareRootDecomposition : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ P : Polynomial K,
    P = (actualPolynomialSquareRootDigit false P) ^ 2 +
      Polynomial.X * (actualPolynomialSquareRootDigit true P) ^ 2


def ActualRationalSquareRootDecomposition : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    f = (actualRationalSquareRootDigit false f) ^ 2 +
      RatFunc.X * (actualRationalSquareRootDigit true f) ^ 2

def ActualRationalSquareRootUniqueness : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ a b c d : RatFunc K,
    a ^ 2 + RatFunc.X * b ^ 2 = c ^ 2 + RatFunc.X * d ^ 2 → a = c ∧ b = d

def ActualDifferentialCartierCharacterization : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ a b : RatFunc K,
    actualDifferentialCartier (a ^ 2 + RatFunc.X * b ^ 2) = b


def ActualDifferentialCartierSquarePullout : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f g : RatFunc K,
    actualDifferentialCartier (g ^ 2 * f) = g * actualDifferentialCartier f

def ActualDifferentialCartierLocalPowers : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K,
    (RatFunc.X - RatFunc.C z : RatFunc K) ≠ 0 ∧
    ∀ k : Int,
      actualDifferentialCartier (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k)) = 0 ∧
      actualDifferentialCartier (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k + 1)) =
        RatFunc.C ((frobeniusEquiv K 2).symm b) * (RatFunc.X - RatFunc.C z) ^ k


def EvenSelectorIdentity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    actualDifferentialCartier (RatFunc.X * f) = actualRationalSquareRootDigit false f

/-- Integer-power local rules include every pole order and polynomial power.
Supporting lem:binary-transient and thm:residue-observer, not either whole result. -/
def EvenSelectorLocalPowers : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K, ∀ k : Int,
    actualDifferentialCartier
      (RatFunc.X * (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k))) =
        RatFunc.C ((frobeniusEquiv K 2).symm b) * (RatFunc.X - RatFunc.C z) ^ k ∧
    actualDifferentialCartier
      (RatFunc.X * (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k + 1))) =
        RatFunc.C ((frobeniusEquiv K 2).symm (z * b)) *
          (RatFunc.X - RatFunc.C z) ^ k
end LogicLineages.CartierObserverCurrent.Thin.Targets
