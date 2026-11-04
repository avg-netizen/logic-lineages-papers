module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.ScheduledWordTargets
public import LogicLineages.OrdinalComparison.ActualTailSeparation
public import LogicLineages.OrdinalComparison.ScheduledCountProof
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof

theorem scheduledJointOrder : Targets.ScheduledJointOrder := by
  intro small big a b
  induction b using Ordinal.lt_wf.induction generalizing a small big with
  | h b ih =>
    intro hab heps hbudget
    have hae := hab.trans_lt heps
    by_cases hf : a < Ordinal.omega0
    · rw [(actualScheduledCountRecursion small a hae).1 hf]
      exact Nat.zero_le _
    · have hna := le_of_not_gt hf
      have hnb := hna.trans hab
      have hda := actualNonfiniteDecomposition a hna hae
      have hdb := actualNonfiniteDecomposition b hnb heps
      have hstep : actualControlledStep (fun _ => small 0) a ≤
          actualControlledStep (fun _ => big 0) b := by
        exact actualMaximumJointMonotone (actualLimitPart a) (actualLimitPart b)
          hda.2.1.bot_lt (actualLimitPartMonotone hab) hdb.1 (small 0) (big 0) (hbudget 0)
      have hd := actualControlledStepStrict (fun _ => big 0) b hnb heps
      have hrec := ih (actualControlledStep (fun _ => big 0) b) hd
        (a := actualControlledStep (fun _ => small 0) a)
        (small := fun i => small (i+1)) (big := fun i => big (i+1))
        hstep (hd.trans heps) (fun i => hbudget (i+1))
      rw [(actualScheduledCountRecursion small a hae).2 hna,
        (actualScheduledCountRecursion big b heps).2 hnb]
      exact Nat.add_le_add_right hrec 1

private theorem strictMono_nat_gap (f : Nat → Nat) (hf : StrictMono f) (x k : Nat) :
    f x+k ≤ f (x+k) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hs : f (x+k)+1 ≤ f (x+(k+1)) := Nat.succ_le_of_lt (hf (by omega))
    omega

private theorem four_mul_output_succ (B : Nat) : 4*Phi B < Phi (B+1) := by
  have h4 : 4*Phi B < 2^(Phi B+2) := by
    have hh := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := Phi B)) (by decide : 0 < 4)
    simpa [pow_add,Nat.mul_comm] using hh
  have he : Phi B+2 ≤ 2^(Phi B+1) := by
    have hh := Nat.lt_two_pow_self (n := Phi B+1)
    omega
  exact h4.trans_le ((Nat.pow_le_pow_right (by decide) he).trans (Phi_succ_gap B))

theorem controlBudgetShiftOrder : Targets.ControlBudgetShiftOrder := by
  intro B V a b hBV ha i
  have hV := CounterLeaderBounds.Proof.four_mul_lt_Phi V
  have hB : 4*Phi B < Phi V :=
    (four_mul_output_succ B).trans_le (Phi_strictMono.monotone (Nat.succ_le_of_lt hBV))
  have hfirst : Phi B+a ≤ Phi V := by omega
  have hm := (Phi_strictMono.iterate i).monotone hfirst
  have hg := strictMono_nat_gap (Phi^[i]) (Phi_strictMono.iterate i) (Phi B) a
  have hi : (Phi^[i+1]) B+a ≤ (Phi^[i+1]) V := by
    simpa only [Function.iterate_succ_apply] using hg.trans hm
  unfold sourceBudget
  omega

theorem sourceInputMassOrder : Targets.SourceInputMassOrder := by
  intro d c e t u _ hce htu he
  have hp := Phi_strictMono.monotone htu
  have hcu : c ≤ Phi u := by omega
  have hbudget : ∀ i : Nat, sourceBudget e t i ≤ sourceBudget c u i := by
    intro i
    have hi := (Phi_strictMono.iterate (i+1)).monotone htu
    unfold sourceBudget
    omega
  have hc := scheduledJointOrder (sourceBudget e t) (sourceBudget c u)
    (Ordinal.omega0 ^ (d : Ordinal)) (Ordinal.omega0 ^ (d : Ordinal)) le_rfl
    (finiteOmegaPowerBelowEpsilonZero d) hbudget
  change sourceCount d e t ≤ sourceCount d c u at hc
  have hi : (Phi^[sourceCount d e t]) u ≤ (Phi^[sourceCount d c u]) u :=
    iterate_index_mono (fun x => (self_lt_Phi x).le) u hc
  refine ⟨hcu,hc,?_,?_⟩
  · change (Phi^[sourceCount d e t]) t ≤ (Phi^[sourceCount d c u]) u
    exact ((Phi_strictMono.iterate (sourceCount d e t)).monotone htu).trans hi
  · intro hlt
    change (Phi^[sourceCount d e t]) t < (Phi^[sourceCount d c u]) u
    exact ((Phi_strictMono.iterate (sourceCount d e t)) hlt).trans_le hi

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof
