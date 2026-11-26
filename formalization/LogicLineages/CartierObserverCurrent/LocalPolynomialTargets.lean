module
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic.Targets

/-- Literal inverse-power local rule plus actual Cartier on embedded polynomials.
This does not assert a power-series or Laurent-series expansion theorem. -/
def LocalPolePolynomialRule : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    (∀ z b : K, ∀ j : Nat,
      actualDifferentialCartier (rationalC b / (rationalX - rationalC z) ^ (2 * j)) = 0 ∧
      actualDifferentialCartier (rationalC b / (rationalX - rationalC z) ^ (2 * j + 1)) =
        rationalC ((frobeniusEquiv K 2).symm b) /
          (rationalX - rationalC z) ^ (j + 1)) ∧
    (∀ P : Polynomial K,
      actualDifferentialCartier (algebraMap (Polynomial K) (RatFunc K) P) =
        algebraMap (Polynomial K) (RatFunc K) (actualPolynomialSquareRootDigit true P) ∧
      ∀ n : Nat, (actualPolynomialSquareRootDigit true P).coeff n =
        (frobeniusEquiv K 2).symm (P.coeff (2 * n + 1)))
end LogicLineages.CartierObserverCurrent.Basic.Targets
