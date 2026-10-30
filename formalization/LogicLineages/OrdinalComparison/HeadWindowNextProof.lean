module
public import LogicLineages.OrdinalComparison.HeadWindowTargets
public import LogicLineages.OrdinalComparison.HeadEndpointProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixMaximumProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualLeastNextLimit : Targets.ActualLeastNextLimit := by
  intro mu lam hlam hlt
  have hd := Ordinal.isSuccLimit_sub hlam.isSuccPrelimit hlt
  calc
    mu + Ordinal.omega0 ≤ mu + (lam - mu) :=
      add_le_add_right (Ordinal.omega0_le_of_isSuccLimit hd) mu
    _ = lam := Ordinal.add_sub_cancel_of_le hlt.le

private theorem limitPart_limit_add_nat (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualNextLimitHeadFacts : Targets.ActualNextLimitHeadFacts := by
  intro mu hmu hlimit
  have hdiv : Ordinal.omega0 ^ (1 : Ordinal) ∣ mu := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlimit.isSuccPrelimit)
  have hmin : actualMinExponentAtLeast mu 1 := (actualMinExponentDivisibility mu hmu 1).mpr hdiv
  have homega : Ordinal.omega0 < epsilonZero := by
    simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1
  have hbound : Ordinal.omega0 < Ordinal.omega0 ^ ((1 : Ordinal) + 1) := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono
        (show (1 : Ordinal) < 1 + 1 from Order.lt_add_one_iff.mpr le_rfl)
  have hnormomega : actualOrdinalNorm Ordinal.omega0 = 2 := by
    simpa only [Nat.cast_one, mul_one, Nat.cast_zero, add_zero, Nat.mul_one, Nat.add_zero] using
      actualFiniteHeadNorm 1 0
  have hsum := actualDivisiblePrefixNormAddition mu Ordinal.omega0 hmu homega 1 hdiv hbound
  have hnorm : actualOrdinalNorm (mu + Ordinal.omega0) = actualOrdinalNorm mu + 2 := by
    rw [hsum.2, hnormomega]
  have hsumlimit : Order.IsSuccLimit (mu + Ordinal.omega0) :=
    Ordinal.isSuccLimit_add mu Ordinal.isSuccLimit_omega0
  refine ⟨hsum.1, hsumlimit, hnorm, ?_⟩
  intro t ht
  have hi := actualHeadInputFacts (mu + Ordinal.omega0) hsum.1 hsumlimit t (by omega)
  have hbudget : actualOrdinalNorm mu ≤ Phi t := ht.trans (self_lt_Phi t).le |>.trans' (by omega)
  have hsmall : 2 ≤ Phi t - actualOrdinalNorm mu := by have h := self_lt_Phi t; omega
  have hstep : actualDescentStep (actualHeadInitial (mu + Ordinal.omega0) t) =
      actualHeadInitial mu (Phi t) := by
    unfold actualDescentStep
    rw [show actualLimitPart (actualHeadInitial (mu + Ordinal.omega0) t) = mu + Ordinal.omega0 from
      limitPart_limit_add_nat _ hsumlimit _]
    rw [hi.2.2, actualDivisiblePrefixMaximum mu Ordinal.omega0 hmu homega
      Ordinal.omega0_pos 1 hmin hbound (Phi t) hbudget]
    have hfin := actualFiniteHeadMaximum 0 (Phi t - actualOrdinalNorm mu) (by simpa using hsmall)
    simpa only [actualHeadInitial, Nat.zero_add, Nat.cast_one, mul_one, Nat.cast_zero, mul_zero, zero_add,
      Nat.mul_zero, Nat.sub_zero] using congrArg (fun x : Ordinal => mu + x) hfin
  have hrec := (actualTerminalRecursion (actualHeadInitial (mu + Ordinal.omega0) t) hi.1).2 hi.2.1
  have he := congrArg (fun p : Nat × Nat => p.1) hrec
  have hc := congrArg (fun p : Nat × Nat => p.2) hrec
  change actualHeadEndpoint (mu + Ordinal.omega0) t =
    actualTerminalValue (actualDescentStep (actualHeadInitial (mu + Ordinal.omega0) t)) at he
  change actualHeadCount (mu + Ordinal.omega0) t =
    actualReplacementCount (actualDescentStep (actualHeadInitial (mu + Ordinal.omega0) t)) + 1 at hc
  have hv := actualDescentStepCollapse (actualHeadInitial (mu + Ordinal.omega0) t) hi.2.1 hi.1
  rw [hstep] at he hc hv
  exact ⟨hstep, he, hc, hv⟩

theorem actualCommonNormHeadOrder : Targets.ActualCommonNormHeadOrder := by
  intro mu lam hmu hlam hmulim hlamlim hmule t htmu htlam
  have hi := actualHeadInputFacts mu hmu hmulim t htmu
  have hj := actualHeadInputFacts lam hlam hlamlim t htlam
  have horder : actualHeadInitial mu t ≤ actualHeadInitial lam t := by
    rcases lt_or_eq_of_le hmule with hlt | rfl
    · have htail : ((t - actualOrdinalNorm mu : Nat) : Ordinal) < lam - mu :=
        Ordinal.natCast_lt_of_isSuccLimit (Ordinal.isSuccLimit_sub hlamlim.isSuccPrelimit hlt) _
      exact (Ordinal.lt_sub.mp htail).le.trans le_self_add
    · exact le_rfl
  have hc : actualHeadCount mu t ≤ actualHeadCount lam t :=
    actualReplacementCountJointMonotone _ _ horder hj.1 (by rw [hi.2.2, hj.2.2])
  have hx := actualHeadCompleteCount mu hmu hmulim t htmu
  have hy := actualHeadCompleteCount lam hlam hlamlim t htlam
  have he : actualHeadEndpoint mu t ≤ actualHeadEndpoint lam t := by
    rw [hx.2.2.2.2.1, hy.2.2.2.2.1]
    exact (iterate_index_mono (fun x => (self_lt_Phi x).le) t) hc
  refine ⟨hc, he, ?_⟩
  rw [hx.2.2.2.2.2, hy.2.2.2.2.2]
  exact Nat.add_le_add he hc

end LogicLineages.OrdinalComparison
