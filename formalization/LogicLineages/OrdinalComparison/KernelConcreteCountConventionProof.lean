module
public import LogicLineages.OrdinalComparison.KernelConcreteCountConventionScheduleProof
public import LogicLineages.OrdinalComparison.WholeScheduledCountProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConcreteCountConvention.Proof
open KernelReachableInputConvention
attribute [local irreducible] Phi fastControl

theorem discrepancy (t : Nat) (ht : 4 ≤ t) : CountDiscrepancy t := by
  have hq := KernelReachableInputConvention.Proof.numerical_facts t ht
  have hf := KernelReachableInputConvention.Proof.first_data t ht
  have hs := KernelReachableInputConvention.Proof.second_data t ht
  have heps : Ordinal.omega0 ^ (2 : Ordinal) < epsilonZero := by
    simpa only [Nat.cast_ofNat] using finiteOmegaPowerBelowEpsilonZero 2
  have hpos : (0 : Ordinal) < (2 : Ordinal) := by norm_num
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hpos)
  have hn := Ordinal.omega0_le_of_isSuccLimit hlim
  have hfirst : actualMaximumPredecessor (Ordinal.omega0 ^ (2 : Ordinal)) (budget t 0) = sharedState t := by
    exact hf.2.2.2.2
  have hsecond : actualMaximumPredecessor (sharedState t) (budget t 1) = limitState t := by
    exact hs.2.2.1
  have hpq : (0 : Ordinal) < (coefficient t : Ordinal) := by exact_mod_cast (by omega : 0 < coefficient t)
  have hll : Order.IsSuccLimit (limitState t) :=
    Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hpq
  have hshared : sharedState t < epsilonZero := by
    simpa only [sharedState,Nat.cast_one] using
      (actualFiniteTailClosureNorm (limitState t) (KernelReachableInputConvention.Proof.limit_below t) 1).1
  have hsharedn : Ordinal.omega0 ≤ sharedState t :=
    (Ordinal.omega0_le_of_isSuccLimit hll).trans le_self_add
  have hcount : wholeCount t = WholeScheduledCount.count
      (fun i => budget t ((i+1)+1)) (limitState t) + 1 + 1 := by
    unfold wholeCount
    rw [(WholeScheduledCount.Proof.exactRecursion (budget t) _ heps).2 hn,hfirst]
    rw [(WholeScheduledCount.Proof.exactRecursion (fun i => budget t (i+1)) _ hshared).2 hsharedn]
    rw [hsecond]
  have hlower : coefficient t ≤ WholeScheduledCount.count
      (fun i => budget t ((i+1)+1)) (limitState t) := by
    apply WholeScheduledCount.Proof.uniformLinearLowerBound (coefficient t) _ _ le_rfl
      (KernelReachableInputConvention.Proof.limit_below t)
    intro i
    have hb := budget_lower t ((i+1)+1)
    change 2*coefficient t ≤ budget t ((i+1)+1)
    have hbf : firstBudget t = Phi t-1 := rfl
    omega
  have hc := (companion_data t ht).2.2
  unfold CountDiscrepancy
  rw [hcount]
  omega

theorem exactWholeCountDiscrepancy : Targets.ExactWholeCountDiscrepancy := discrepancy 4 (by decide)
end LogicLineages.OrdinalComparison.KernelConcreteCountConvention.Proof
