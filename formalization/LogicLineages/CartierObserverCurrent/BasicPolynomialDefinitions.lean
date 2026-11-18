module
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.FieldTheory.Perfect

@[expose] public section

universe u

namespace LogicLineages.CartierObserverCurrent.Basic

/-- Literal finite polynomial Lambda_b: retain coefficient 2n+b at exponent n.
The finite bound enumerates every potentially nonzero retained coefficient. -/
noncomputable def actualBinaryPolynomialDigit {K : Type u} [Field K] (b : Bool)
    (P : Polynomial K) : Polynomial K :=
  ∑ n ∈ Finset.range (P.natDegree + 1), Polynomial.monomial n (P.coeff (Nat.bit b n))

/-- Actual even/odd coefficient selection followed by the unique square-root
field automorphism, as needed for the source differential Cartier operator. -/
noncomputable def actualPolynomialSquareRootDigit {K : Type u} [Field K]
    [CharP K 2] [PerfectRing K 2] (b : Bool) (P : Polynomial K) : Polynomial K :=
  (actualBinaryPolynomialDigit b P).map (frobeniusEquiv K 2).symm.toRingHom

end LogicLineages.CartierObserverCurrent.Basic
