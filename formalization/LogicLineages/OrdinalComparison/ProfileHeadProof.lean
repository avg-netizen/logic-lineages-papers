module
public import LogicLineages.OrdinalComparison.ProfileHeadTargets
public import LogicLineages.OrdinalComparison.ActualTailSeparation
public import LogicLineages.OrdinalComparison.ActualSinglePredecessor
public import LogicLineages.OrdinalComparison.ReserveStageInputProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem profile_head_growth (rho : NONote) (hl : Order.IsSuccLimit rho.1.repr) (n : Nat) :
    Phi (actualOrdinalNorm rho.1.repr + n) < actualProfileHead rho n := by
  have he := normalRepresentationSound rho
  have hrec := actualSinglePredecessorRecurrence rho.1.repr he hl n
  have hm := actualMaximumPredecessor_correct rho.1.repr hl.bot_lt he
    (Phi (actualOrdinalNorm rho.1.repr + n))
  have hn := actualLimitMaximumPredecessorSaturation rho.1.repr he hl
    (Phi (actualOrdinalNorm rho.1.repr + n))
  have hc := actualCollapseDominatesNorm _ (hm.1.1.trans he)
  change Phi (actualOrdinalNorm rho.1.repr + n) < actualCollapse (rho.1.repr + (n : Ordinal))
  rw [hrec]
  rw [hn] at hc
  omega

theorem actualFixedLimitProfileHeads : Targets.ActualFixedLimitProfileHeads := by
  intro rho hl
  have hs := actualTailSeparation rho.1.repr (normalRepresentationSound rho) hl
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    exact (show actualProfileHead rho n < 2 ^ actualProfileHead rho n from Nat.lt_two_pow_self).trans
      (hs.1 n)
  · intro n
    exact (Nat.le_add_left n (actualOrdinalNorm rho.1.repr)).trans_lt
      ((self_lt_Phi _).trans (profile_head_growth rho hl n))

theorem actualOmegaProfileHead : Targets.ActualOmegaProfileHead := by
  have hr : profileOmegaNote.1.repr = Ordinal.omega0 := by
    simp [profileOmegaNote, ONote.repr]
  refine ⟨hr, ?_⟩
  intro n
  have hl : Order.IsSuccLimit profileOmegaNote.1.repr := by rw [hr]; exact Ordinal.isSuccLimit_omega0
  have hg := profile_head_growth profileOmegaNote hl n
  have htwo := reserveStageTwoMulLtPhi (actualOrdinalNorm profileOmegaNote.1.repr + n)
  exact (Nat.mul_le_mul_left 2 (Nat.le_add_left n (actualOrdinalNorm profileOmegaNote.1.repr))).trans_lt
    (htwo.trans hg)

end LogicLineages.OrdinalComparison
