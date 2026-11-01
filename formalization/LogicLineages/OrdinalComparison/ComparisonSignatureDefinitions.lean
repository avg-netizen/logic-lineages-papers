module
public import LogicLineages.OrdinalComparison.EncodedNormBallDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
public import LogicLineages.OrdinalComparison.PrincipalBlocksDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Conservative finite source principal-exponent carrier: a full actual
normal-norm ball. It may contain unused indices, including zero. It does not
assert a unique minimal original signature or compare norms by ordinal order. -/
def encodedComparisonSignatureRank (budget eta : Nat) : Nat :=
  ((encodedNormalNormBall budget).filter (fun n => rawComparisonCode n eta=0)).length

end LogicLineages.OrdinalComparison
