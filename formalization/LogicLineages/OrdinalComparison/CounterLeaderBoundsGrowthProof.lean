module
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsResidualProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionExpansionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderBounds.Proof
open CounterLeaderExpansion

/-- A whole-domain consequence of the literal control's shifted exponential bound. -/
theorem four_mul_lt_Phi (u : Nat) : 4*u < Phi u := by
  have hp : 4*u < 2^(u+2) := by
    have h := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := u)) (by decide : 0 < 4)
    simpa [pow_add, Nat.mul_comm] using h
  have hm : 2^(u+2) ≤ 2^(u+100) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact hp.trans_le (hm.trans (two_pow_shift_le_Phi u))

theorem strictActualLeaderBounds : Targets.StrictActualLeaderBounds := by
  intro n c t ht
  have hold : CounterLeaderExpansion.threshold n c ≤ t :=
    (Nat.le_max_left _ _).trans ht
  have htail : 2*c+10 ≤ t := (Nat.le_max_right _ _).trans ht
  have hs := actualResidualBounds.1 n c t
  have hp := actualResidualBounds.2 n c t ht
  obtain ⟨heven,hsub,hidentity⟩ :=
    CounterLeaderExpansion.Proof.exactCounterLeaderIdentity n c t hold
  have heven' : leader n c t % 2 = 0 := Nat.even_iff.mp heven
  have hg : 4 * leaderPreimage n c t < leader n c t :=
    four_mul_lt_Phi (leaderPreimage n c t)
  constructor <;> omega

end LogicLineages.OrdinalComparison.CounterLeaderBounds.Proof
