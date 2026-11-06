module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.LetterProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- The actual source counter is bridged only on c+d+1 ≤ t. The companion
quadratic lower bound is used after, not instead of, that explicit bridge. -/
theorem sourceCounterGrowth (d c t : Nat) (hd : 2 ≤ d) (ht : c+d+1 ≤ t) :
    2 ^ t ≤ sourceCount d c t := by
  have hb := Focused.sourceProcessBridge d c t (by omega) ht
  have hc := CounterResidualDivergence.Proof.actualFiniteDegreeLowerCount.1 d c t hd ht
  have hq := CounterLeaderExpansion.Proof.quadraticCount c t (by omega)
  have hp : 4 * 2 ^ t ≤ Phi t := by
    calc
      4 * 2 ^ t = 2 ^ (t+2) := by simp only [pow_add]; norm_num; omega
      _ ≤ 2 ^ (t+100) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ Phi t := two_pow_shift_le_Phi t
  have htPow : t < 2 ^ t := Nat.lt_two_pow_self
  change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t ≤
    actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t at hc
  rw [hq] at hc
  rw [hb.1]
  omega

theorem letterGrowth : Targets.LetterGrowth := by
  intro D a t ha hnon ht
  have hdom := (WordGuardCompletion.Proof.letterTailCorrect D a t ha ht).1
  refine ⟨hdom,?_⟩
  have hPhi : 2 ^ t ≤ Phi t :=
    (Nat.pow_le_pow_right (by decide) (by omega : t ≤ t+100)).trans
      (two_pow_shift_le_Phi t)
  rcases a with ⟨tag,d,c,j⟩
  change tag ≠ 0 at hnon
  change c+d+j.natAbs+4 ≤ t at ht
  by_cases h1 : tag = 1
  · subst tag
    exact hPhi
  · by_cases h2 : tag = 2
    · subst tag
      change (0 : Int) < ((Phi t/2 : Nat) : Int)+j+1 at hdom
      have hi : 1 ≤ (((Phi t/2 : Nat) : Int)+j+1).toNat := by omega
      have hh := iterate_index_mono (fun x => (self_lt_Phi x).le) t hi
      change 2 ^ t ≤ rawQuadraticShift j t
      exact hPhi.trans (by simpa only [Function.iterate_one, rawQuadraticShift] using hh)
    · have hnot : ¬ tag ≤ 2 := by omega
      have hallowed : (tag = 3 ∨ tag = 4) ∧ 3 ≤ d ∧ d ≤ D := by
        simpa only [LetterAllowed, hnot, if_false] using ha
      rcases hallowed.1 with h3 | h4
      · subst tag
        change c ≤ Phi t ∧ 0 < sourceSignedDepth d c j t at hdom
        have hi : 1 ≤ (sourceSignedDepth d c j t).toNat := by omega
        have hh := iterate_index_mono (fun x => (self_lt_Phi x).le) t hi
        change 2 ^ t ≤ sourceSignedValue d c j t
        exact hPhi.trans (by simpa only [Function.iterate_one, sourceSignedValue] using hh)
      · subst tag
        exact sourceCounterGrowth d c t (by omega) (by omega)

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
