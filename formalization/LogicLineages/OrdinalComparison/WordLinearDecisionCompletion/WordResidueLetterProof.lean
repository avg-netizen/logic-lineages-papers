module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueTargets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.LetterProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.AssemblyProof
public import LogicLineages.OrdinalComparison.ControlResidueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
open PolynomialGraphCompletion KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Positive iteration retains the literal final Phi input; no scheduler
identification is needed for the range letters. -/
theorem positiveIterateResidue (m t k : Nat) (hm : 0 < m) (ht : m ≤ t)
    (hk : 0 < k) : Int.ModEq (m : Int) ((Phi^[k]) t : Int) (fastControlResidue m : Int) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Function.iterate_succ_apply']
  apply Int.natCast_modEq_iff.mpr
  apply phiShiftedConstantResidues m hm
  have hg := iterate_self_le (fun x => (self_lt_Phi x).le) n t
  omega

theorem literalLetterResidue : Targets.LiteralLetterResidue := by
  intro D m hm a ha t ht
  have hg : WordGuardCompletion.letterTail a ≤ t := by unfold letterTail at ht; omega
  have hm' : m ≤ t := by unfold letterTail at ht; omega
  have hb := WordGuardCompletion.Proof.letterTailCorrect D a t ha hg
  refine ⟨hb.1, ?_⟩
  rcases a with ⟨tag, d, c, j⟩
  by_cases h0 : tag = 0
  · subst tag
    have hp : 0 ≤ (t : Int) + j := hb.1
    change Int.ModEq (m : Int) (((t : Int) + j).toNat : Int) (1 * (t : Int) + j)
    rw [Int.toNat_of_nonneg hp, one_mul]
  · by_cases h1 : tag = 1
    · subst tag
      simpa [letterValue, letterAffine] using
        (Int.natCast_modEq_iff.mpr (phiShiftedConstantResidues m hm t (by omega)))
    · by_cases h2 : tag = 2
      · subst tag
        have hp : 0 < ((Phi t / 2 : Nat) : Int) + j + 1 := hb.1
        have hk : 0 < (((Phi t / 2 : Nat) : Int) + j + 1).toNat := by omega
        simpa [letterValue, letterAffine, rawQuadraticShift] using
          positiveIterateResidue m t _ hm hm' hk
      · have hlarge : ¬ tag ≤ 2 := by omega
        have he : (tag = 3 ∨ tag = 4) ∧ 3 ≤ d ∧ d ≤ D := by
          simpa only [LetterAllowed, hlarge, if_false] using ha
        rcases he.1 with h3 | h4
        · subst tag
          have hp : 0 < sourceSignedDepth d c j t := hb.1.2
          have hk : 0 < (sourceSignedDepth d c j t).toNat := by omega
          simpa [letterValue, letterAffine, sourceSignedValue] using
            positiveIterateResidue m t _ hm hm' hk
        · subst tag
          have hr : residueTail d c 0 m ≤ t := by
            change WordGuardCompletion.letterTail (4, d, c, j) + m +
              residueTail d c 0 m ≤ t at ht
            omega
          have hs := KernelSourceCompletion.Proof.correctedKernelResidues.1 d c 0
            (Or.inl (by omega)) m (by omega) t hr
          have hn : Nat.ModEq m (sourceCount d c t) (kernelCounterResidue d c m) := by
            change sourceCount d c t % m = kernelCounterResidue d c m % m
            rw [hs.2.2.2.2, Nat.mod_eq_of_lt hs.2.2.2.1]
          simpa [letterValue, letterAffine] using Int.natCast_modEq_iff.mpr hn

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
