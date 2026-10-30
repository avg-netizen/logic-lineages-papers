module
public import LogicLineages.OrdinalComparison.OmegaBlockTargets
public import LogicLineages.OrdinalComparison.OmegaBlockOrdinalProof
public import LogicLineages.OrdinalComparison.PartitionEnvelopeProof
public import LogicLineages.OrdinalComparison.ControlScheduleProof
public import LogicLineages.OrdinalComparison.GrowingBudgetPrefixProof
public import LogicLineages.OrdinalComparison.ControlResidueProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem compensated_mass_iteration (c n i : Nat) :
    c + ((compensatedPrefixControl c)^[i]) n = (Phi^[i]) (c + n) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change c + (Phi (c + ((compensatedPrefixControl c)^[i]) n) - c) = _
    rw [Nat.add_sub_of_le ((Nat.le_add_right c _).trans (self_lt_Phi _).le), ih]

theorem actualNumericalOmegaBlock : Targets.ActualNumericalOmegaBlock := by
  intro c u m hu hm hBlarge hmB
  let g := compensatedPrefixControl c
  let a := actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c)
  let B := Phi u
  let d := B - c - 1
  let r := Ordinal.omega0 ^ (d : Ordinal)
  let H := actualOmegaCopyCount c u
  let C := Phi (u + 1)
  let Q := restrictedPartitionPeriod d m
  have hOmega := actualOmegaOmegaFacts
  have hi := actualHeadInputFacts _ hOmega.1 hOmega.2.1 (u - c) (by rw [hOmega.2.2]; omega)
  have hfirst := actualOmegaBlockFirstStep c u hu
  have hd : 1 ≤ d := hfirst.1
  have hrε : r < epsilonZero := finiteOmegaPowerBelowEpsilonZero d
  have hrnorm : actualOrdinalNorm r = B - c := by
    have hn := hfirst.2.2.1
    rw [hfirst.2.1] at hn
    exact hn
  have hH : H = actualControlledCount g r + 1 := hfirst.2.2.2
  have hHpos : 0 < H := by omega
  have hQpos : 0 < Q := Nat.mul_pos (Nat.factorial_pos d) (pow_pos (by omega : 0 < m) _)
  have hQbound : Q ≤ 2 ^ (2 ^ B) :=
    restrictedPartitionDoubleExponentBound B d m hBlarge hd (by dsimp [d]; omega) hm hmB
  have hC : c ≤ C := by have hh := self_lt_Phi (u + 1); dsimp [C]; omega
  have hCmod : Nat.ModEq Q C (fastControlResidue Q) := phiNextInputResidueEnvelope Q hQpos u hQbound
  let budget := fun i : Nat => Phi (c + actualOrdinalNorm (actualControlledStateAfter g r i))
  have hstream : (fun i => budget i - c) = actualControlBudgetStream g r := rfl
  have hcount : actualScheduledCount (fun i => budget i - c) r = actualControlledCount g r := by
    rw [hstream]
    exact actualControlBudgetStreamCount g r hrε
  have hlive : ∀ i : Nat, i < actualScheduledCount (fun j => budget j - c) r →
      c + actualOrdinalNorm (actualScheduledStateAfter (fun j => budget j - c) r i) ≤ budget i ∧
        Nat.ModEq Q (budget i) C := by
    intro i hidx
    rw [hcount] at hidx
    have hs : actualScheduledStateAfter (fun j => budget j - c) r i = actualControlledStateAfter g r i := by
      rw [hstream]
      exact actualControlBudgetStreamTrace g r i
    rw [hs]
    have hnorm := actualControlledNormIteration g r hrε i hidx.le
    have hiter : actualOrdinalNorm r ≤ (g^[i]) (actualOrdinalNorm r) := by
      have h := (iterate_index_mono (fun n => ((compensatedPrefixControlBounds c).2 n).2.le)
        (actualOrdinalNorm r)) (Nat.zero_le i)
      simpa only [Function.iterate_zero_apply] using h
    have hmass : B ≤ c + actualOrdinalNorm (actualControlledStateAfter g r i) := by
      rw [hnorm]
      rw [hrnorm] at hiter ⊢
      have hh := self_lt_Phi u
      dsimp [B] at *
      omega
    have hlarge : Q ≤ 2 ^ (2 ^ (c + actualOrdinalNorm (actualControlledStateAfter g r i) + 100)) :=
      hQbound.trans (Nat.pow_le_pow_right (by decide)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hres := fastControlDoubleExponentResidueEnvelope Q hQpos
      (c + actualOrdinalNorm (actualControlledStateAfter g r i) + 100) 5 (by omega) (by decide) hlarge
    refine ⟨(self_lt_Phi _).le, ?_⟩
    exact hres.trans hCmod.symm
  have htransfer := actualNumericalCongruentBudgetTransfer d m c C 0 hd hm hC budget (by
    simpa only [Nat.cast_zero, add_zero] using hlive)
  simp only [Nat.cast_zero, add_zero] at htransfer
  rw [hcount] at htransfer
  have hmod : Nat.ModEq m H (1 + restrictedPartitionCount d (C - c)) := by
    rw [hH]
    simpa only [Nat.add_comm] using htransfer.add (Nat.ModEq.refl 1)
  have htrace := actualControlledTraceFirstFinite g a hi.1
  have hnormend := actualControlledNormIteration g a hi.1 H le_rfl
  refine ⟨hmod, hHpos, htrace.1, ?_, ?_⟩
  · intro i hidx
    exact (htrace.2 i hidx.le).2.2 hidx
  · change c + actualOrdinalNorm (actualControlledStateAfter g a H) = (Phi^[H]) u
    rw [hnormend, hi.2.2]
    have h := compensated_mass_iteration c (u - c) H
    rw [Nat.add_sub_of_le (by omega : c ≤ u)] at h
    exact h

end LogicLineages.OrdinalComparison
