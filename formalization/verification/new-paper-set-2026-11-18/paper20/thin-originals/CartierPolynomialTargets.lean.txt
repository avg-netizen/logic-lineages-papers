module
public import LogicLineages.OrdinalComparison.CartierPolynomialDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Polynomial suppliers for the literal rational square decomposition in
paper10, source460–466. Rational Cartier semantics remain separate. -/
def ActualPolynomialSquareRootDigitCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ b : Bool, ∀ P : Polynomial K, ∀ n : Nat,
      ((actualPolynomialSquareRootDigit b P).coeff n) ^ 2 = P.coeff (Nat.bit b n)

def ActualPolynomialSquareRootDecomposition : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ P : Polynomial K,
    P = (actualPolynomialSquareRootDigit false P) ^ 2 +
      Polynomial.X * (actualPolynomialSquareRootDigit true P) ^ 2

end LogicLineages.OrdinalComparison.Targets
