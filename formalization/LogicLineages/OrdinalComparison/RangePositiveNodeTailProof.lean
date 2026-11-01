module
public import LogicLineages.OrdinalComparison.RangePositiveNodeProgramProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionKernelImageProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

attribute [local irreducible] encodedCollectedNormalize encodedAffineProfileCertificateTail encodedRangeAffineTail

theorem local_domain_bound (source positive profile : Nat) :
    encodedOneVariableComparisonDomainBound source≤encodedRangePositiveLocalTail source positive profile :=
  Nat.le_max_left _ _

theorem local_range_bound (source : Nat) (P : FixedLimitPositiveExpr)
    (hP : fixedLimitProfileBelow epsilonZero P) (profile : Nat) :
    collectedRangeThreshold (collectedPositiveNormalize P)≤
      encodedRangePositiveLocalTail source (positiveExprEncode P) profile := by
  have heq := encodedCollectedNormalizeCorrect P hP
  unfold encodedRangePositiveLocalTail
  rw [heq]
  dsimp only
  rw [collectedRangeThresholdCode.2 (collectedPositiveNormalize P)]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem local_affine_bound (source : Nat) (P : FixedLimitPositiveExpr)
    (hP : fixedLimitProfileBelow epsilonZero P) (profile c b : Nat) (tags : CollectedPositiveTags)
    (hNF : collectedPositiveNormalize P=.mk c b tags) :
    encodedRangeAffineTail source b c≤encodedRangePositiveLocalTail source (positiveExprEncode P) profile := by
  unfold encodedRangePositiveLocalTail
  rw [encodedCollectedNormalizeCorrect P hP,hNF]
  simp only [collectedPositiveEncode,Nat.unpair_pair]
  exact (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

theorem local_affine_profile_bound (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hP : fixedLimitProfileBelow epsilonZero P) (eta : NONote) (mass profile c b : Nat)
    (tags : CollectedPositiveTags) (hNF : collectedPositiveNormalize P=.mk c b tags) :
    encodedAffineProfileCertificateTail (rawNoteEncode (comparisonPrincipalNote eta).1) profile mass b c≤
      encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range (w++[(eta,mass)]) A)) (positiveExprEncode P) profile := by
  unfold encodedRangePositiveLocalTail
  rw [encodedCollectedNormalizeCorrect P hP,hNF,ComparisonExpansion.outer_source w eta mass A]
  simp only [collectedPositiveEncode,Nat.unpair_pair]
  rw [←(LimitPairCertificate.principal_source.2 eta).2]
  exact (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

end LogicLineages.OrdinalComparison.RangePositiveNode
