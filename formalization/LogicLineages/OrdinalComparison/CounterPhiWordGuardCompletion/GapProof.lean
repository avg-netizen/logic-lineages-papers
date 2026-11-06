module
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.LeaderProof
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Even the nearest distinct Phi inputs pay a factor-four output separation. -/
theorem four_Phi_gap (v u : Nat) (hvu : v < u) : 4*Phi v < Phi u := by
  have hp : 4*Phi v < 2^(Phi v+2) := by
    have h := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := Phi v))
      (by decide : 0 < 4)
    simpa [pow_add, Nat.mul_comm] using h
  have hi : Phi v+2 ≤ 2^(Phi v+1) := by
    have h := Nat.lt_two_pow_self (n := Phi v+1)
    omega
  have he := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hi
  exact hp.trans_le (he.trans ((Phi_succ_gap v).trans
    (Phi_strictMono.monotone (Nat.succ_le_of_lt hvu))))

/-- Bridge and rational leader bounds at the actual original counter input. -/
theorem sourceCounterBounds (n c K t : Nat) (ht : counterTail n c K ≤ t) :
    t ≤ wordValue (leaderWord n c) t ∧
    Phi (wordValue (leaderWord n c) t) < 2*sourceCount (n+3) c t ∧
    4*sourceCount (n+3) c t < 3*Phi (wordValue (leaderWord n c) t) ∧ K ≤ t := by
  have hbound : CounterLeaderBounds.threshold n c ≤ t := (Nat.le_max_left _ _).trans ht
  have hlead : CounterWordGuardCompletion.leaderTail n c ≤ t :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
  have hp : c+(n+3)+1+K ≤ t := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ht)
  have hb := Focused.sourceProcessBridge (n+3) c t (by omega) (by omega)
  have hl := CounterWordGuardCompletion.Proof.leaderWord_value n c t hlead
  have hs := CounterLeaderBounds.Proof.strictActualLeaderBounds n c t hbound
  have hg : t ≤ CounterLeaderExpansion.leaderPreimage n c t :=
    (CounterLeaderExpansion.Proof.bottomInput_ge n c t).trans
      (CounterLeaderExpansion.Proof.kernel_ge 3 (c+3) (CounterLeaderExpansion.bottomInput n c t))
  rw [hl,hb.1]
  exact ⟨hg,hs.1,hs.2,by omega⟩

theorem quantitativeCounterPhiGap : Targets.QuantitativeCounterPhiGap := by
  intro n c K t v ht hv
  have hb := sourceCounterBounds n c K t ht
  have hvK : K ≤ v := by unfold rangeTail at hv; omega
  have hg := CounterLeaderBounds.Proof.four_mul_lt_Phi v
  have hlo (h : wordValue (leaderWord n c) t ≤ v) : sourceCount (n+3) c t+K < Phi v := by
    have hm := Phi_strictMono.monotone h
    omega
  have hhi (h : v < wordValue (leaderWord n c) t) : Phi v+K < sourceCount (n+3) c t := by
    have hm := four_Phi_gap v (wordValue (leaderWord n c) t) h
    omega
  constructor
  · constructor
    · intro h
      by_contra hn
      have hh := hhi (by omega)
      omega
    · exact hlo
  · constructor
    · intro h
      by_contra hn
      have hh := hlo (by omega)
      omega
    · exact hhi

end LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
