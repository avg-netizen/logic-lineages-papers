module
public import LogicLineages.CartierObserverCurrent.ActualPeriodTargets
import LogicLineages.CartierObserverCurrent.PeriodStateTupleProof
import LogicLineages.CartierObserverCurrent.PeriodTupleExactProof
import LogicLineages.OrdinalComparison.Control
public meta import LogicLineages.Audit

public section
namespace LogicLineages.CartierObserverCurrent.ActualPeriod
open LogicLineages.OrdinalComparison

/-- The printed half exponent is the linked one, by unfolding names only. -/
theorem halfExponentPrinted (u : Nat) :
    actualLinkedHalfExponent u = Nat.log 2 (Phi u) - 1 := by
  rw [actualLinkedHalfExponent.eq_1, actualLinkedBinaryExponent.eq_1, actualLinkedBudget.eq_1]

theorem linkedSourceBound (v : Nat) (hv : 4 ≤ v) : 5 ≤ Phi v := by
  have := self_lt_Phi v
  omega

theorem linkedExactPeriod (v : Nat) (hv : 4 ≤ v) :
    Function.minimalPeriod (actualResidueTupleFrobenius (Phi v)) (actualResidueTuple (Phi v)) =
      2 * (Nat.log 2 (Phi (Phi v)) - 1) := by
  rw [← halfExponentPrinted (Phi v)]
  exact PeriodTupleFacts.actualExact (Phi v) (linkedSourceBound v hv)

theorem exactTuplePeriod : Targets.ExactTuplePeriod := by
  intro v hv
  exact linkedExactPeriod v hv

/-- Coincidence divisibility at the literal printed parameters, without
the target's local abbreviations. -/
theorem coincidenceDivides (v : Nat) (hv : 4 ≤ v) (j p : Nat)
    (hstates :
      (actualDifferentialCartier (K := ActualResidueField))^[j + p]
          (actualLinkedDifferential (Phi v)) =
        (actualDifferentialCartier (K := ActualResidueField))^[j]
          (actualLinkedDifferential (Phi v))) :
    2 * (Nat.log 2 (Phi (Phi v)) - 1) ∣ p := by
  have hper := PeriodStateTuple.statePeriodic (Phi v) (linkedSourceBound v hv) j p hstates
  have hdvd := hper.minimalPeriod_dvd
  rw [linkedExactPeriod v hv] at hdvd
  exact hdvd

theorem eventualDivides (v : Nat) (hv : 4 ≤ v) (p : Nat)
    (hp : ∃ j : Nat, ∀ k : Nat,
      (actualDifferentialCartier (K := ActualResidueField))^[j + k + p]
          (actualLinkedDifferential (Phi v)) =
        (actualDifferentialCartier (K := ActualResidueField))^[j + k]
          (actualLinkedDifferential (Phi v))) :
    2 * (Nat.log 2 (Phi (Phi v)) - 1) ∣ p := by
  obtain ⟨j, hj⟩ := hp
  exact coincidenceDivides v hv j p (by simpa only [Nat.add_zero] using hj 0)

theorem actualStateCoincidence : Targets.ActualStateCoincidence := by
  intro v hv
  exact coincidenceDivides v hv

theorem eventualPeriodDivisibility : Targets.EventualPeriodDivisibility := by
  intro v hv
  exact eventualDivides v hv

theorem completeActualPeriod : Targets.CompleteActualPeriod :=
  ⟨exactTuplePeriod, actualStateCoincidence, eventualPeriodDivisibility⟩

#audit_namespace LogicLineages.CartierObserverCurrent.ActualPeriod
end LogicLineages.CartierObserverCurrent.ActualPeriod
