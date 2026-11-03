module
public import LogicLineages.OrdinalComparison.KernelConcreteCountConventionTargets
public import LogicLineages.OrdinalComparison.KernelReachableInputConventionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConcreteCountConvention.Proof
open KernelReachableInputConvention
attribute [local irreducible] Phi fastControl

theorem first_budget (t : Nat) : budget t 0 = Phi t - 1 := rfl

theorem second_budget (t : Nat) : budget t 1 = Phi (Phi t) - 1 := rfl

theorem budget_lower (t i : Nat) : Phi t - 1 ≤ budget t i := by
  have hi : t ≤ (Phi^[i]) t := iterate_self_le (fun z => (self_lt_Phi z).le) i t
  unfold budget
  rw [Function.iterate_succ_apply']
  exact Nat.sub_le_sub_right (Phi_strictMono.monotone hi) 1

theorem companion_data (t : Nat) (ht : 4 ≤ t) : CompanionData t := by
  have hc := CounterLeaderExpansion.Proof.quadraticCount 1 t (by omega)
  have hq := KernelReachableInputConvention.Proof.numerical_facts t ht
  have he := Nat.even_iff.mp (CounterLeaderExpansion.Proof.phiEven t)
  refine ⟨first_budget t,second_budget t,?_⟩
  change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) 1 t = _
  rw [hc]
  dsimp only [coefficient,firstBudget] at *
  omega

theorem exactCompanionCount : Targets.ExactCompanionCount := companion_data 4 (by decide)
end LogicLineages.OrdinalComparison.KernelConcreteCountConvention.Proof
