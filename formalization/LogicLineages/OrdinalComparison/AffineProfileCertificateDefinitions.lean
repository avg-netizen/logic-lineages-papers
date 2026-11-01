module
public import LogicLineages.OrdinalComparison.ProfileCompositionDefinitions
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramDefinitions
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal binary P1 tree for a*x+b; no affine extension of the source
syntax is assumed. -/
def positiveAffineProfile (a b : Nat) : FixedLimitPositiveExpr :=
  .add (positiveInputMultiple a) (.constant b)

def positiveAffineProfileCode (a b : Nat) : Nat :=
  4*Nat.pair (positiveInputMultipleCode a) (4*b)+2

/-- Actual computable modulus for the affine leaf of the source simultaneous
limit-cut certificate; it computes the entire requested composed profile. -/
def encodedAffineProfileCertificateTail (L P c a b : Nat) : Nat :=
  max (encodedProfileSupplierTail L
    (encodedProfileCompose P (positiveAffineProfileCode a b))) (c+rawNormCode L)

end LogicLineages.OrdinalComparison
