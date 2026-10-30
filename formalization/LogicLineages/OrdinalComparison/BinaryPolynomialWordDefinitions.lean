module
public import LogicLineages.OrdinalComparison.BinaryQuotientTargets

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- Actual repeated numerator updates for the binary observer. Bits are read
least significant first, in precisely the order of actualBinarySeriesWord. -/
noncomputable def actualBinaryPolynomialWord {K : Type u} [Field K]
    (A : Polynomial K) : List Bool → Polynomial K → Polynomial K
  | [], U => U
  | b :: w, U => actualBinaryPolynomialWord A w (actualBinaryPolynomialDigit b (U * A))

end LogicLineages.OrdinalComparison
