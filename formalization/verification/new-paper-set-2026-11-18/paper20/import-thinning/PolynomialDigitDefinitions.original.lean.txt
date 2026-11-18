module
public import LogicLineages.OrdinalComparison.SeriesContinuationDefinitions

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- Literal finite polynomial Lambda_b: retain coefficient 2n+b at exponent n.
The finite bound enumerates every potentially nonzero retained coefficient. -/
noncomputable def actualBinaryPolynomialDigit {K : Type u} [Field K] (b : Bool)
    (P : Polynomial K) : Polynomial K :=
  ∑ n ∈ Finset.range (P.natDegree + 1), Polynomial.monomial n (P.coeff (Nat.bit b n))

end LogicLineages.OrdinalComparison
