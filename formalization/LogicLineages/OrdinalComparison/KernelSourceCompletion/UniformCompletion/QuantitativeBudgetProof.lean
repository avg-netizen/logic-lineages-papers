module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeTargets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSuppliersProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof

/-- A strictly increasing natural map preserves every additive input gap. -/
theorem strictMono_nat_add (f : Nat → Nat) (hf : StrictMono f) (x a : Nat) :
    f x+a ≤ f (x+a) := by
  induction a with
  | zero => exact le_rfl
  | succ a ih =>
    have hs : f (x+a)+1 ≤ f (x+(a+1)) := Nat.succ_le_of_lt (hf (by omega))
    omega

theorem four_mul_Phi_lt_succ (t : Nat) : 4*Phi t < Phi (t+1) := by
  have h4 : 4*Phi t < 2^(Phi t+2) := by
    have hh := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := Phi t))
      (by decide : 0 < 4)
    simpa [pow_add,Nat.mul_comm] using hh
  have he : Phi t+2 ≤ 2^(Phi t+1) := by
    have hh := Nat.lt_two_pow_self (n := Phi t+1)
    omega
  exact h4.trans_le ((Nat.pow_le_pow_right (by decide) he).trans (Phi_succ_gap t))

theorem shiftedSourceBudgetOrder : Targets.ShiftedSourceBudgetOrder := by
  intro t a b ha i
  have hgap := four_mul_Phi_lt_succ t
  have hfirst : Phi t+a ≤ Phi (t+1) := by omega
  have hm := (Phi_strictMono.iterate i).monotone hfirst
  have hg := strictMono_nat_add (Phi^[i]) (Phi_strictMono.iterate i) (Phi t) a
  have hi : (Phi^[i+1]) t+a ≤ (Phi^[i+1]) (t+1) := by
    simpa only [Function.iterate_succ_apply] using hg.trans hm
  unfold sourceBudget
  omega

theorem source_cross_counts (d c e t : Nat) (hc : c ≤ Phi t) :
    sourceCount d e t ≤ sourceCount d c (t+1) := by
  exact Focused.scheduledJointOrder (sourceBudget e t) (sourceBudget c (t+1))
    (Ordinal.omega0 ^ (d : Ordinal)) (Ordinal.omega0 ^ (d : Ordinal)) le_rfl
    (finiteOmegaPowerBelowEpsilonZero d) (shiftedSourceBudgetOrder t c e hc)

theorem source_cross_value (d c e t : Nat) (hc : c ≤ Phi t) :
    sourceValue d e t < sourceValue d c (t+1) := by
  have hcount := source_cross_counts d c e t hc
  change (Phi^[sourceCount d e t]) t < (Phi^[sourceCount d c (t+1)]) (t+1)
  exact ((Phi_strictMono.iterate (sourceCount d e t)) (Nat.lt_succ_self t)).trans_le
    (iterate_index_mono (fun x => (self_lt_Phi x).le) (t+1) hcount)

theorem broadSourceBlock : Targets.BroadSourceBlock := by
  intro n c t hb
  dsimp only
  let K := sourceValue (n+2) (c+n+2) t
  have hcut := Focused.broadUnsignedBlockCut.2 n c t hb
  dsimp only at hcut
  have hdom : c+(n+1)+1 ≤ K := by have hh := hcut.1; omega
  have hbridge := Focused.sourceProcessBridge (n+1) c K (by omega) hdom
  constructor
  · exact hcut.2.2.2.2.2.2.trans hbridge.2.1.symm
  · rw [hcut.2.2.2.2.2.1,hbridge.1]

theorem sourceBlock_step (n c t : Nat) (hb : c+n+2 ≤ Phi t) :
    sourceValue (n+2) c t =
      sourceValue (n+1) c (sourceValue (n+2) (c+n+2) t) :=
  (broadSourceBlock n c t hb).1

theorem source_block (d c t : Nat) (hd : 2 ≤ d) (hb : c+d ≤ Phi t) :
    sourceValue d c t = sourceValue (d-1) c (sourceValue d (c+d) t) := by
  have hp : d-2+2 = d := by omega
  have hc : d-2+1 = d-1 := by omega
  simpa only [Nat.add_assoc,hp,hc] using
    sourceBlock_step (d-2) c t (by omega)

theorem source_value_lower (d c t : Nat) (hd : 1 ≤ d) (hc : c ≤ Phi t) :
    Phi t ≤ sourceValue d c t := by
  have hcal := Focused.firstBudgetCalibration d c t hd hc
  have hp : 1 ≤ sourceCount d c t := by have hh := hcal.2.2.2.2.1; omega
  change (Phi^[1]) t ≤ (Phi^[sourceCount d c t]) t
  exact iterate_index_mono (fun x => (self_lt_Phi x).le) t hp

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof
