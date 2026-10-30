module
public import LogicLineages.OrdinalComparison.ActualCartierPeriodTargets
public import LogicLineages.OrdinalComparison.CartierOrbitProof
public import LogicLineages.OrdinalComparison.ResidueTupleProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualCompleteCartierPeriodDivisibility : Targets.ActualCompleteCartierPeriodDivisibility := by
  intro u hu j p hstates
  have hper : Function.IsPeriodicPt (actualResidueTupleFrobenius u) p (actualResidueTuple u) := by
    funext z
    rw [actualResidueTupleIterate]
    have h := congrArg (fun f : RatFunc ActualResidueField =>
      (actualTranslatedRationalEmbedding z.val f).coeff (-1)) hstates
    rw [actualDifferentialCartierIteratedResidue, actualDifferentialCartierIteratedResidue,
      actualLinkedDifferentialInitialResidue u hu z,
      iterateFrobeniusEquiv_symm_add_apply] at h
    have hp := (iterateFrobeniusEquiv ActualResidueField 2 j).symm.injective h
    have hforward := congrArg (iterateFrobeniusEquiv ActualResidueField 2 p) hp
    simp only [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def] at hforward
    exact hforward.symm
  rw [← actualResidueTupleExactPeriod u hu]
  exact hper.minimalPeriod_dvd

theorem fullActualSourceCartierPeriod : Targets.FullActualSourceCartierPeriod := by
  intro v hv
  have hu : 5 ≤ Phi v := by have := self_lt_Phi v; omega
  constructor
  · exact actualResidueTupleExactPeriod (Phi v) hu
  · exact actualCompleteCartierPeriodDivisibility (Phi v) hu

end LogicLineages.OrdinalComparison
