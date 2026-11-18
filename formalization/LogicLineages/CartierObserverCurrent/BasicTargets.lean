module
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic.Targets

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
      rationalX * (actualRationalSquareRootDigit true f) ^ 2

def ActualRationalSquareRootUniqueness : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ a b c d : RatFunc K,
    a ^ 2 + rationalX * b ^ 2 = c ^ 2 + rationalX * d ^ 2 → a = c ∧ b = d

def ActualDifferentialCartierCharacterization : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ a b : RatFunc K,
    actualDifferentialCartier (a ^ 2 + rationalX * b ^ 2) = b


def ActualDifferentialCartierSquarePullout : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f g : RatFunc K,
    actualDifferentialCartier (g ^ 2 * f) = g * actualDifferentialCartier f

def ActualDifferentialCartierLocalPowers : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K,
    (rationalX - rationalC z : RatFunc K) ≠ 0 ∧
    ∀ k : Int,
      actualDifferentialCartier (rationalC b * (rationalX - rationalC z) ^ (2 * k)) = 0 ∧
      actualDifferentialCartier (rationalC b * (rationalX - rationalC z) ^ (2 * k + 1)) =
        rationalC ((frobeniusEquiv K 2).symm b) * (rationalX - rationalC z) ^ k


def EvenSelectorIdentity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    actualDifferentialCartier (rationalX * f) = actualRationalSquareRootDigit false f

/-- Integer-power local rules include every pole order and polynomial power.
Supporting lem:binary-transient and thm:residue-observer, not either whole result. -/
def EvenSelectorLocalPowers : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K, ∀ k : Int,
    actualDifferentialCartier
      (rationalX * (rationalC b * (rationalX - rationalC z) ^ (2 * k))) =
        rationalC ((frobeniusEquiv K 2).symm b) * (rationalX - rationalC z) ^ k ∧
    actualDifferentialCartier
      (rationalX * (rationalC b * (rationalX - rationalC z) ^ (2 * k + 1))) =
        rationalC ((frobeniusEquiv K 2).symm (z * b)) *
          (rationalX - rationalC z) ^ k
end LogicLineages.CartierObserverCurrent.Basic.Targets
