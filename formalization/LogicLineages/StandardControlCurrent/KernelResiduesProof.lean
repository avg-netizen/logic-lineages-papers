module
public import LogicLineages.StandardControlCurrent.KernelResiduesTargets
public import LogicLineages.StandardControlCurrent.NumericalKernelBaseProof
public import LogicLineages.OrdinalComparison.KernelCounterResidueProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.KernelResiduesProof
open OrdinalComparison NumericalKernel KernelSourceCompletion

theorem padded : KernelResiduesTargets.PaddedTail := by
  intro d c m hd hm t ht
  have hdom : c+d+1 ≤ t := (Nat.le_max_right _ _).trans ht
  exact ⟨hdom,NumericalKernelProof.padded d c t hd hdom⟩

theorem counter : KernelResiduesTargets.CounterResidue := by
  intro d c m hd hm
  have h := KernelCounterResidueProof.effectiveActualKernelCounterResidue d c m hd hm
  refine ⟨h.1,?_⟩
  intro t ht
  have hp := padded d c m hd hm t ht
  rw [hp.2.1]
  exact ⟨h.2 t ht,KernelCounterResidueProof.actualKernelCounterCongruence d c m hd hm t ht⟩

theorem signed_residue : KernelResiduesTargets.SignedResidue := by
  intro d c j hj m hm t ht
  have hd : 1 ≤ d := by rcases hj with h | ⟨h,_⟩ <;> omega
  have hdom : c+d+1 ≤ t := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
  have h := SignedKernelDomainProof.correctedSignedKernelResidues d c j hj m hm t ht
  have hc := NumericalKernelProof.depth_agreement d c t hd hdom j
  have hv : signed d c j t = rawSignedKernelValue d c j t := by
    unfold signed rawSignedKernelValue
    rw [hc]
  simpa only [hc,hv] using h

theorem budgets : KernelResiduesTargets.BudgetResidues := by
  intro d c m hd hm t ht i
  have hQ := KernelCounterCalibrationProof.kernelPeriodPositive d m hd hm
  have hdom : c+d+1 ≤ t := (Nat.le_max_right _ _).trans ht
  have hqt : restrictedPartitionPeriod d m ≤ t := (Nat.le_max_left _ _).trans ht
  have hi : t ≤ (Phi^[i]) t := iterate_self_le (fun x => (self_lt_Phi x).le) i t
  have hs := self_lt_Phi ((Phi^[i]) t)
  rw [Function.iterate_succ_apply']
  refine ⟨hs,by omega,?_⟩
  exact fullUniformResidueEnvelopes.2.2.1 _ hQ.1 _ (hqt.trans hi)

theorem full : KernelResiduesTargets.Full := by
  refine ⟨counter,signed_residue,padded,budgets,?_,?_,?_⟩
  · exact ⟨KernelCounterCalibrationProof.kernelPeriodPositive,
      KernelCounterCalibrationProof.kernelModularDifferenceCorrect,
      KernelCounterCalibrationProof.partitionInputCongruence⟩
  · exact ⟨RestrictedPartitionEvaluationProof.restrictedPartitionEvaluatorExact,
      RestrictedPartitionEvaluationProof.primitiveRecursivePartitionEvaluator.2.1,
      KernelCounterResidueProof.primitiveRecursiveKernelArithmetic⟩
  · exact ⟨KernelCounterResidueProof.primitiveRecursiveKernelResidue.1,
      KernelCounterResidueProof.primitiveRecursiveKernelResidue.2,
      SignedKernelDomainProof.fixedSignedKernelThresholdPrimitiveRecursive,
      fastControlResiduePrimitiveRecursive⟩
end LogicLineages.StandardControlCurrent.KernelResiduesProof
