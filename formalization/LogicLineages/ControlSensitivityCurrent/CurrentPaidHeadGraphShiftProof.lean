module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationTargets
public import LogicLineages.ControlSensitivityCurrent.FullAdditionProof
public import LogicLineages.OrdinalComparison.HeadWindowNextProof
public import LogicLineages.PermittedControl.CollapseProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

open LogicLineages.OrdinalComparison

/-- Affordable prefix/finite-tail computation, with the actual given f. -/
theorem exactStep : Targets.ExactStep := by
  intro f hf μ hμ hlimit
  -- The first three conclusions are ordinal facts independent of the
  -- control in the historical fourth conclusion, which is not used.
  have ho := actualNextLimitHeadFacts μ hμ hlimit
  refine ⟨ho.1,ho.2.1,ho.2.2.1,?_⟩
  intro t ht
  have hdiv : Ordinal.omega0 ^ (1 : Ordinal) ∣ μ := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlimit.isSuccPrelimit)
  have hmin := (actualMinExponentDivisibility μ hμ 1).mpr hdiv
  have homega : Ordinal.omega0 < epsilonZero := by
    simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1
  have hbound : Ordinal.omega0 < Ordinal.omega0 ^ ((1 : Ordinal)+1) := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono
        (show (1 : Ordinal) < 1+1 from Order.lt_add_one_iff.mpr le_rfl)
  have hself := (FullAddition.completeAddition.2.2.2 f hf).2.1 t
  have hnorm := ho.2.2.1
  have hbudget : actualOrdinalNorm μ ≤ f t := by omega
  have hsmall : 2 ≤ f t - actualOrdinalNorm μ := by omega
  have hfin := actualFiniteHeadMaximum 0 (f t - actualOrdinalNorm μ) (by simpa using hsmall)
  have hp : actualMaximumPredecessor (μ+Ordinal.omega0) (f t) = actualHeadInitial μ (f t) := by
    rw [actualDivisiblePrefixMaximum μ Ordinal.omega0 hμ homega
      Ordinal.omega0_pos 1 hmin hbound (f t) hbudget]
    simpa only [actualHeadInitial,Nat.zero_add,Nat.cast_one,mul_one,Nat.cast_zero,mul_zero,
      zero_add,Nat.mul_zero,Nat.sub_zero] using congrArg (fun x : Ordinal => μ+x) hfin
  have hi : actualOrdinalNorm (μ+Ordinal.omega0) + (t-actualOrdinalNorm (μ+Ordinal.omega0)) = t := by omega
  have hm := (FullAddition.completeAddition.2.2.2 f hf).1
  have hr := PermittedControl.singlePredecessor f hm hf.1 (μ+Ordinal.omega0) ho.1 ho.2.1
    (t-actualOrdinalNorm (μ+Ordinal.omega0))
  refine ⟨hp,?_⟩
  unfold J actualHeadInitial
  rw [hr,hi,hp] <;> rfl

theorem exactIteration : Targets.ExactIteration := by
  intro f hf β he hl δ
  induction δ with
  | zero =>
    simp only [shiftHead,Nat.cast_zero,mul_zero,add_zero,Function.iterate_zero,id_eq]
    exact ⟨he,hl,True.intro,fun t ht => ⟨ht,True.intro⟩⟩
  | succ δ ih =>
    rcases ih with ⟨hε,hlim,hn,hiter⟩
    have h := exactStep f hf (shiftHead β δ) hε hlim
    have hs : shiftHead β (δ+1) = shiftHead β δ + Ordinal.omega0 := by
      simp only [shiftHead,Nat.cast_add,Nat.cast_one,mul_add_one,add_assoc]
    have hn' : actualOrdinalNorm (shiftHead β (δ+1)) = actualOrdinalNorm β+2*(δ+1) := by
      rw [hs,h.2.2.1,hn]
      omega
    refine ⟨by rw [hs]; exact h.1,by rw [hs]; exact h.2.1,hn',?_⟩
    intro t ht
    have hdom : actualOrdinalNorm (shiftHead β δ+Ordinal.omega0) ≤ t := hs ▸ ht
    have hnorm := h.2.2.1
    have hself := (FullAddition.completeAddition.2.2.2 f hf).2.1 t
    have hi := hiter (f t) (by omega)
    rw [hs,(h.2.2.2 t hdom).2,Function.iterate_succ_apply,hi.2]
    exact ⟨hi.1,by omega⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
