module
public import LogicLineages.OrdinalComparison.LinkedResidueDefinitions
public import LogicLineages.OrdinalComparison.SimplePoleLaurentDefinitions

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- Actual local Laurent expansion of the source differential
X^(e-1)/A_d(X) dX at z, in the translated parameter t=X-z (so dX=dt).
Source targets require u>=5, proving e>=1 before the natural exponent is used. -/
noncomputable def actualLinkedResidueExpansion {K : Type u} [Field K] [Algebra (ZMod 2) K]
    (u : Nat) (z : K) : HahnSeries Int K :=
  actualSimplePoleExpansion
    ((actualBinarySourceDenominator (actualLinkedCutoff u)).map (algebraMap (ZMod 2) K))
    (Polynomial.X ^ (actualLinkedOffset u - 1)) z

end LogicLineages.OrdinalComparison
