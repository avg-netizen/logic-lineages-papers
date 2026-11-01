module
public import LogicLineages.OrdinalComparison.AffineProfileCertificateDefinitions
public import LogicLineages.OrdinalComparison.CollectedPositiveDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Source P/P affine terminal rule, in the SAME0/1/2 sign encoding as the
whole sign theorem. The displayed tail is independent of the slopes. -/
def encodedAffineSourceSign (a b c d : Nat) : Nat × Nat :=
  ((if a<c then 0 else if c<a then 2 else if b<d then 0 else if d<b then 2 else 1),b+d+1)

end LogicLineages.OrdinalComparison
