module
public import LogicLineages.OrdinalComparison.AdjacentTransportTargets
public import LogicLineages.OrdinalComparison.CompensatedSyncProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualControlledEndpointAlongTrace : Targets.ActualControlledEndpointAlongTrace := by
  intro g A he i hi
  have hc := actualControlledCountTraceDecomposition g A he i hi
  change ((actualControlledStep g)^[actualControlledCount g (actualControlledStateAfter g A i)])
      (((actualControlledStep g)^[i]) A) = ((actualControlledStep g)^[actualControlledCount g A]) A
  rw [hc, Function.iterate_add_apply]

theorem actualWorstMassKernelMonotone : Targets.ActualWorstMassKernelMonotone := by
  intro beta hb he t u ht htu
  let pi := Ordinal.omega0 ^ beta
  let N := actualOrdinalNorm pi
  have hu : N ≤ u := ht.trans htu
  have hinit (v : Nat) (hv : N ≤ v) : actualSuffixKernelInitial pi (v-N) v=pi := by
    have hz : v-(v-N)-N=0 := by omega
    change pi+((v-(v-N)-N : Nat) : Ordinal)=pi
    rw [hz, Nat.cast_zero, add_zero]
  have hcal (v : Nat) (hv : N ≤ v) : actualSuffixKernel pi (v-N) v =
      (v-N)+actualOrdinalNorm (actualControlledStateAfter (compensatedPrefixControl (v-N)) pi
        (actualControlledCount (compensatedPrefixControl (v-N)) pi)) := by
    have hd : v-N+actualOrdinalNorm pi ≤ v := (Nat.sub_add_cancel hv).le
    have htrace := actualSuffixKernelTrace beta hb he (v-N) v hd
    have hexit := htrace.2.1 (actualSuffixKernelCount pi (v-N) v) le_rfl
    change (v-N)+actualOrdinalNorm (actualControlledStateAfter (compensatedPrefixControl (v-N))
      (actualSuffixKernelInitial pi (v-N) v) (actualSuffixKernelCount pi (v-N) v)) =
      actualSuffixKernel pi (v-N) v at hexit
    simpa only [actualSuffixKernelCount, hinit v hv] using hexit.symm
  have hsync := actualCompensatedSynchronizedTraces (t-N) (u-N) pi pi le_rfl he le_rfl
    (by change t-N+N ≤ u-N+N; rw [Nat.sub_add_cancel ht, Nat.sub_add_cancel hu]; exact htu)
  rw [hcal t ht, hcal u hu]
  exact hsync.2.2

end LogicLineages.OrdinalComparison
