module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordAlgebraProof
import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSmallKernelsProof
import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedProcessBridgeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordSemanticProof
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion
open WordAlgebraProof

/-- Each emitted source symbol has its actual domain, and the count row
retains the complete count rather than only the terminal norm. -/
theorem callSymbolCorrect (p : Call) (t : Nat) (hd : 1 ≤ p.1)
    (ht : p.2+p.1+1 ≤ t) :
    LetterDomain (rangeLetter p) t ∧
    letterValue (rangeLetter p) t =
      actualSuffixKernel (Ordinal.omega0 ^ (p.1 : Ordinal)) p.2 t ∧
    UnaryDomain (countContribution p) t ∧
    unaryValue (countContribution p) t =
      2*(actualSuffixKernelCount (Ordinal.omega0 ^ (p.1 : Ordinal)) p.2 t : Int) := by
  rcases p with ⟨d,c⟩
  change 1 ≤ d at hd
  change c+d+1 ≤ t at ht
  by_cases h1 : d = 1
  · subst d
    have hs := Focused.actualOmegaSuffixKernel c t (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [rangeLetter, phiLetter, LetterDomain]
    · simpa [rangeLetter, phiLetter, letterValue] using hs.2.symm
    · simp [countContribution, UnaryDomain]
    · simp [countContribution, unaryValue, hs.1]
  · by_cases h2 : d = 2
    · subst d
      let q : Nat := (c+1)/2
      have hc : actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t =
          Phi t/2-q+1 := Focused.actualOmegaSquaredSuffixCount c t (by omega)
      have hPhi := self_lt_Phi t
      have hsub : q ≤ Phi t/2 := by dsimp only [q]; omega
      have hpos : 0 < actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t := by
        rw [hc]
        omega
      have hdepth : ((Phi t/2 : Nat) : Int) + -(q : Int) + 1 =
          (actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t : Int) := by
        rw [hc]
        omega
      have hdepthpos : (0 : Int) < ((Phi t/2 : Nat) : Int) + -(q : Int) + 1 := by
        rw [hdepth]
        exact_mod_cast hpos
      have hquad : rawQuadraticShift (-(q : Int)) t =
          actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) c t := by
        unfold rawQuadraticShift actualSuffixKernel
        rw [hdepth]
        simp only [Int.toNat_natCast]
      have heven : Phi t % 2 = 0 := Nat.even_iff.mp (Focused.actualPhiEven t)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [rangeLetter, quadraticLetter, LetterDomain, q] using hdepthpos
      · simpa [rangeLetter, quadraticLetter, letterValue, q] using hquad
      · simp [countContribution, UnaryDomain, WordDomain, phiLetter, LetterDomain]
      · simp [countContribution, unaryValue, wordValue, phiLetter, letterValue]
        rw [hc]
        dsimp only [q] at *
        omega
    · have hs := Focused.sourceProcessBridge d c t hd ht
      have hmass : c ≤ Phi t := by have hPhi := self_lt_Phi t; omega
      have hpos : (0 : Int) < (sourceCount d c t : Int) := by
        exact_mod_cast hs.2.2.2.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [rangeLetter, h1, h2, kernelLetter, LetterDomain, sourceSignedDepth] using
          And.intro hmass hpos
      · simpa [rangeLetter, h1, h2, kernelLetter, letterValue, sourceSignedValue,
          sourceSignedDepth, sourceValue] using hs.2.1
      · simp [countContribution, h1, h2, UnaryDomain, WordDomain,
          counterLetter, LetterDomain, hmass]
      · simp [countContribution, h1, h2, unaryValue, wordValue,
          counterLetter, letterValue, hs.1]

theorem callCompilationCorrect : Targets.CallCompilationCorrect := by
  intro calls
  induction calls with
  | nil =>
      intro t _ _
      constructor
      · simp [compileCalls, UnaryDomain, WordDomain]
      · simp [compileCalls, unaryValue, wordValue, callRun]
  | cons p calls ih =>
      intro t hdegrees hgenuine
      have hp := hdegrees p (List.mem_cons_self)
      have hs := callSymbolCorrect p t hp hgenuine.1
      let z := actualSuffixKernel (Ordinal.omega0 ^ (p.1 : Ordinal)) p.2 t
      have hr := ih z
        (fun q hq => hdegrees q (List.mem_cons_of_mem p hq)) hgenuine.2
      have hstep : wordValue [rangeLetter p] t = z := hs.2.1
      have hword : WordDomain [rangeLetter p] t := ⟨hs.1, trivial⟩
      change UnaryDomain (addUnary (countContribution p)
          (prepend [rangeLetter p] (compileCalls calls))) t ∧ _
      refine ⟨addUnary_domain _ _ t hs.2.2.1
        (prepend_domain _ _ t hword (by simpa only [hstep] using hr.1)), ?_⟩
      change unaryValue (addUnary (countContribution p)
          (prepend [rangeLetter p] (compileCalls calls))) t = _
      rw [addUnary_value, prepend_value, hstep, hs.2.2.2, hr.2]
      simp only [callRun, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      omega

theorem callSymbolsAllowed (D : Nat) (p : Call) (hd : 1 ≤ p.1) (hbound : p.1 ≤ D) :
    LetterAllowed D (rangeLetter p) ∧ UnaryAllowed D (countContribution p) := by
  rcases p with ⟨d,c⟩
  change 1 ≤ d at hd
  change d ≤ D at hbound
  by_cases h1 : d = 1
  · subst d
    simp [rangeLetter, countContribution, phiLetter, LetterAllowed, UnaryAllowed]
  · by_cases h2 : d = 2
    · subst d
      simp [rangeLetter, countContribution, quadraticLetter, phiLetter,
        LetterAllowed, UnaryAllowed, WordAllowed]
    · have hthree : 3 ≤ d := by omega
      simp [rangeLetter, countContribution, h1, h2, kernelLetter, counterLetter,
        LetterAllowed, UnaryAllowed, WordAllowed, hthree, hbound]

theorem callCompilationDegree : Targets.CallCompilationDegree := by
  intro D calls _
  induction calls with
  | nil =>
      intro _
      simp [compileCalls, UnaryAllowed, WordAllowed]
  | cons p calls ih =>
      intro hdegrees
      have hp := hdegrees p (List.mem_cons_self)
      have hs := callSymbolsAllowed D p hp.1 hp.2
      have hr := ih (fun q hq => hdegrees q (List.mem_cons_of_mem p hq))
      change UnaryAllowed D (addUnary (countContribution p)
        (prepend [rangeLetter p] (compileCalls calls)))
      apply addUnary_allowed D _ _ hs.2
      apply prepend_allowed D _ _ _ hr
      intro a ha
      have heq : a = rangeLetter p := List.mem_singleton.mp ha
      subst a
      exact hs.1

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordSemanticProof
