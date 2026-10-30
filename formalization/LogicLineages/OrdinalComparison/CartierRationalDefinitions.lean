module
public import LogicLineages.OrdinalComparison.CartierPolynomialDefinitions
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- Genuine rational square-root parity part from the canonical fraction:
num/den=(num*den)/den². The field denominator is never an oracle. -/
noncomputable def actualRationalSquareRootDigit {K : Type u} [Field K]
    [CharP K 2] [PerfectRing K 2] (b : Bool) (f : RatFunc K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K)
    (actualPolynomialSquareRootDigit b (f.num * f.denom)) /
      algebraMap (Polynomial K) (RatFunc K) f.denom

/-- Differential Cartier on f dX, represented by its actual rational
coefficient. Its square-decomposition characterization is proved separately. -/
noncomputable def actualDifferentialCartier {K : Type u} [Field K]
    [CharP K 2] [PerfectRing K 2] (f : RatFunc K) : RatFunc K :=
  actualRationalSquareRootDigit true f

end LogicLineages.OrdinalComparison
