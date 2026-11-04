module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.ProcessBridgeProof
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionProof
public import LogicLineages.OrdinalComparison.CounterSourceTheoremProof
public import LogicLineages.OrdinalComparison.KernelCounterResidueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.Proof

theorem signedDomainContract : Targets.SignedDomainContract := by
  refine ⟨SignedKernelDomainProof.degreeOneSignedDomain,
    SignedKernelDomainProof.degreeOneNegativeDepthObstruction,?_⟩
  intro d c j hj t ht
  exact (SignedKernelDomainProof.correctedSignedKernelResidues d c j hj 1 le_rfl t ht).1

theorem correctedKernelRecursion : Targets.CorrectedKernelRecursion := by
  exact ⟨actualOmegaSuffixKernel,actualOmegaSquaredSuffixCount,
    FiniteKernelRecursion.block,FiniteKernelRecursion.signed_block,
    FiniteKernelRecursion.quadratic,FiniteKernelRecursion.programs⟩

theorem correctedCounterSource : Targets.CorrectedCounterSource := by
  exact ⟨CounterSourceTheorem.Proof.wholeCounterLemma,
    CounterSourceTheorem.Proof.uniformTailPrograms⟩

theorem correctedKernelResidues : Targets.CorrectedKernelResidues := by
  refine ⟨?_,KernelCounterResidueProof.primitiveRecursiveKernelResidue.1,?_⟩
  · intro d c j hj m hm t ht
    have hd : 1 ≤ d := by rcases hj with h | ⟨h,_⟩ <;> omega
    have hs : correctedSignedKernelThreshold d c j m ≤ t := (Nat.le_max_left _ _).trans ht
    have hc : kernelCounterThreshold d c m ≤ t := (Nat.le_max_right _ _).trans ht
    have hdom : c+d+1 ≤ t := (Nat.le_max_right _ _).trans hc
    have hb := (sourceProcessBridge d c t hd hdom).1
    have hsign := SignedKernelDomainProof.correctedSignedKernelResidues d c j hj m hm t hs
    have hres := KernelCounterResidueProof.effectiveActualKernelCounterResidue d c m hd hm
    refine ⟨hsign.1,hsign.2,?_,hres.1,?_⟩
    · rw [hb]
      exact KernelCounterResidueProof.actualKernelCounterCongruence d c m hd hm t hc
    · rw [hb]
      exact hres.2 t hc
  · intro j
    exact Primrec.nat_max.comp
      (SignedKernelDomainProof.fixedSignedKernelThresholdPrimitiveRecursive j)
      KernelCounterResidueProof.primitiveRecursiveKernelResidue.2

end LogicLineages.OrdinalComparison.KernelSourceCompletion.Proof
