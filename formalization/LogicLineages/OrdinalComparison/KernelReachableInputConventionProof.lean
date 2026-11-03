module
public import LogicLineages.OrdinalComparison.KernelReachableInputConventionFirstProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelReachableInputConvention.Proof
open KernelConventionDiagnostic

attribute [local irreducible] Phi fastControl

theorem second_data (t : Nat) (ht : 4 ≤ t) : SecondData t := by
  have hq := numerical_facts t ht
  have hposq : (0 : Ordinal) < ((coefficient t) : Ordinal) := by
    exact_mod_cast (by omega : 0 < (coefficient t))
  have hlim : Order.IsSuccLimit (limitState t) :=
    Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hposq
  have hpart : actualLimitPart (sharedState t) = (limitState t) := by
    simpa only [sharedState,Nat.cast_one] using limit_tail (limitState t) hlim 1
  have hbudget : compensatedPrefixControl 1 (actualOrdinalNorm (sharedState t)) = (secondBudget t) := by
    change Phi (1+actualOrdinalNorm (sharedState t))-1 = _
    rw [shared_norm t ht]
    rfl
  have hfirst := (first_data t ht).2.2.2.1
  have hsecond : actualControlledStateAfter (compensatedPrefixControl 1) (initial t) 2 =
      actualMaximumPredecessor (limitState t) (secondBudget t) := by
    rw [show (2 : Nat) = 1+1 from rfl,actualControlledStateAfter_succ,hfirst]
    change actualMaximumPredecessor (actualLimitPart (sharedState t))
      (compensatedPrefixControl 1 (actualOrdinalNorm (sharedState t))) = _
    rw [hpart,hbudget]
  have hnorm : actualOrdinalNorm (limitState t) ≤ (secondBudget t) := by
    rw [limit_norm t]
    have hg := self_lt_Phi (Phi t)
    dsimp only [secondBudget]
    omega
  have hstate : (sharedState t) < epsilonZero := by
    simpa only [sharedState,Nat.cast_one] using (actualFiniteTailClosureNorm (limitState t) (limit_below t) 1).1
  have hstatepos : 0 < (sharedState t) := hlim.bot_lt.trans (Order.lt_add_one_iff.mpr le_rfl)
  have hm := actualMaximumPredecessor_correct (sharedState t) hstatepos hstate (secondBudget t)
  have hw : wholeStep (sharedState t) (secondBudget t) = (limitState t) := by
    apply le_antisymm
    · exact Order.lt_add_one_iff.mp hm.1.1
    · exact hm.2 ⟨Order.lt_add_one_iff.mpr le_rfl,hnorm⟩
  have hs := (actualMaximumPredecessor_correct (limitState t) hlim.bot_lt (limit_below t) (secondBudget t)).1.1
  refine ⟨hbudget,hsecond,hw,?_,?_⟩
  · rw [hsecond]; exact hs
  · rw [hsecond,hw]; exact ne_of_lt hs

theorem exactDifferentSecondSteps : Targets.ExactDifferentSecondSteps :=
  second_data 4 (by decide)

end LogicLineages.OrdinalComparison.KernelReachableInputConvention.Proof
