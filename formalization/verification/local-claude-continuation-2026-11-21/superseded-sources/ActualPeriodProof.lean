module
public import LogicLineages.CartierObserverCurrent.ActualPeriodTargets
public import LogicLineages.CartierObserverCurrent.PeriodLaurentBridgeStatementChecks
public import LogicLineages.OrdinalComparison.ResidueTupleProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ActualPeriod
open LogicLineages.OrdinalComparison

theorem exactTuplePeriod : Targets.ExactTuplePeriod := by
  intro v hv
  have hu : 5 ≤ Phi v := by have := self_lt_Phi v; omega
  exact actualResidueTupleExactPeriod (Phi v) hu

theorem actualStateCoincidence : Targets.ActualStateCoincidence := by
  intro v hv j p hstates
  let u := Phi v
  have hu : 5 ≤ u := by have := self_lt_Phi v; dsimp [u]; omega
  have hper : Function.IsPeriodicPt (actualResidueTupleFrobenius u) p (actualResidueTuple u) := by
    funext z
    rw [actualResidueTupleIterate]
    have h := congrArg (fun f : RatFunc ActualResidueField =>
      (actualTranslatedRationalEmbedding z.val f).coeff (-1)) hstates
    rw [PeriodLaurentBridge.StatementChecks.fixed_iteratedResidue,
      PeriodLaurentBridge.StatementChecks.fixed_iteratedResidue,
      PeriodLaurentBridge.StatementChecks.fixed_initialResidue u hu z,
      iterateFrobeniusEquiv_symm_add_apply] at h
    have hp := (iterateFrobeniusEquiv ActualResidueField 2 j).symm.injective h
    have hforward := congrArg (iterateFrobeniusEquiv ActualResidueField 2 p) hp
    simp only [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def] at hforward
    exact hforward.symm
  rw [← actualResidueTupleExactPeriod u hu]
  exact hper.minimalPeriod_dvd

theorem eventualPeriodDivisibility : Targets.EventualPeriodDivisibility := by
  intro v hv p hp
  obtain ⟨j, hj⟩ := hp
  apply actualStateCoincidence v hv j p
  simpa only [Nat.add_zero] using hj 0

theorem completeActualPeriod : Targets.CompleteActualPeriod :=
  ⟨exactTuplePeriod, actualStateCoincidence, eventualPeriodDivisibility⟩

#audit_namespace LogicLineages.CartierObserverCurrent.ActualPeriod
end LogicLineages.CartierObserverCurrent.ActualPeriod
