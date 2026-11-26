module
public import LogicLineages.OrdinalComparison.PolynomialDigitDefinitions
public import Mathlib.FieldTheory.Perfect

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- Actual even/odd coefficient selection followed by the unique square-root
field automorphism, as needed for the source differential Cartier operator. -/
noncomputable def actualPolynomialSquareRootDigit {K : Type u} [Field K]
    [CharP K 2] [PerfectRing K 2] (b : Bool) (P : Polynomial K) : Polynomial K :=
  (actualBinaryPolynomialDigit b P).map (frobeniusEquiv K 2).symm.toRingHom

end LogicLineages.OrdinalComparison
