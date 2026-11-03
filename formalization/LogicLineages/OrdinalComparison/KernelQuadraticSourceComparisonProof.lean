module
public import LogicLineages.OrdinalComparison.KernelQuadraticSourceComparisonTargets
public import LogicLineages.OrdinalComparison.KernelConcreteCountConventionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelQuadraticSourceComparison.Proof
attribute [local irreducible] Phi fastControl

theorem exactUniformComparison : Targets.ExactUniformComparison := by
  intro t ht
  have hc := CounterLeaderExpansion.Proof.quadraticCount 1 t (by omega)
  have hg := self_lt_Phi t
  have heq : KernelConcreteCountConvention.companionCount t = displayedCount t := by
    change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) 1 t = Phi t / 2
    rw [hc]
    omega
  have hd := (KernelConcreteCountConvention.Proof.discrepancy t ht).2
  exact ⟨heq,heq ▸ hd⟩

theorem noLiteralEqualityTail : Targets.NoLiteralEqualityTail := by
  have hw : ∀ T : Nat, ∃ t : Nat, T ≤ t ∧ 4 ≤ t ∧
      displayedCount t < KernelConcreteCountConvention.wholeCount t := by
    intro T
    refine ⟨max T 4,le_max_left _ _,le_max_right _ _,?_⟩
    exact (exactUniformComparison _ (le_max_right _ _)).2
  refine ⟨hw,?_⟩
  rintro ⟨T,hT⟩
  obtain ⟨t,ht,_,hstrict⟩ := hw T
  rw [hT t ht] at hstrict
  exact (lt_irrefl _ hstrict)
end LogicLineages.OrdinalComparison.KernelQuadraticSourceComparison.Proof
