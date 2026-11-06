module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Every emitted kernel keeps its original finite-degree admission. -/
theorem leaderWord_allowed (D n c : Nat) (hD : n+3 ≤ D) :
    WordAllowed D (leaderWord n c) := by
  induction n with
  | zero =>
      intro a ha
      simp only [leaderWord, List.mem_singleton] at ha
      subst a
      simp [LetterAllowed, kernelLetter, hD]
  | succ n ih =>
      intro a ha
      simp only [leaderWord, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [LetterAllowed, kernelLetter]
        omega
      · exact ih (by omega) a ha

theorem leaderTail_step (n c : Nat) : leaderTail n c ≤ leaderTail (n+1) c := by
  change c+2*(n+3)+1+wordTail (leaderWord n c) ≤
    c+2*(n+1+3)+1+(letterTail (kernelLetter (n+4) (c+n+4) 0)+
      letterOffset (kernelLetter (n+4) (c+n+4) 0)+wordTail (leaderWord n c))
  omega

/-- Each calibration invokes the original-schedule bridge at its reached input. -/
theorem source_zero_kernel (d c t : Nat) (hd : 1 ≤ d) (ht : c+d+1 ≤ t) :
    sourceSignedValue d c 0 t = CounterLeaderExpansion.kernel d c t := by
  have hb := Focused.sourceProcessBridge d c t hd ht
  simpa [sourceSignedValue, sourceSignedDepth, sourceValue,
    CounterLeaderExpansion.kernel] using hb.2.1

theorem leaderWord_value (n c t : Nat) (ht : leaderTail n c ≤ t) :
    wordValue (leaderWord n c) t = CounterLeaderExpansion.leaderPreimage n c t := by
  induction n generalizing t with
  | zero =>
      have hb : c+3+3+1 ≤ t := by
        unfold leaderTail at ht
        omega
      change sourceSignedValue 3 (c+3) 0 t = CounterLeaderExpansion.kernel 3 (c+3) t
      exact source_zero_kernel 3 (c+3) t (by omega) hb
  | succ n ih =>
      have hb : c+n+4+(n+4)+1 ≤ t := by
        unfold leaderTail at ht
        omega
      have hs := source_zero_kernel (n+4) (c+n+4) t (by omega) hb
      have hg : t ≤ CounterLeaderExpansion.kernel (n+4) (c+n+4) t := by
        exact iterate_self_le (fun x => (self_lt_Phi x).le) _ t
      have hn : leaderTail n c ≤ CounterLeaderExpansion.kernel (n+4) (c+n+4) t :=
        (leaderTail_step n c).trans (ht.trans hg)
      change wordValue (leaderWord n c) (sourceSignedValue (n+4) (c+n+4) 0 t) = _
      rw [hs, ih _ hn]
      rfl

theorem leaderWordCorrect : Targets.LeaderWordCorrect := by
  intro D n c t hD ht
  have ha := leaderWord_allowed D n c hD
  have hd := WordGuardCompletion.Proof.wordTailCorrect D (leaderWord n c) t ha
    (by unfold leaderTail at ht; omega)
  exact ⟨ha,hd.1,leaderWord_value n c t ht⟩

private theorem counterNodes_append (A B : Word) :
    counterNodes (A++B) = counterNodes A+counterNodes B := by
  simp [counterNodes, List.filter_append]

private theorem leaderWord_no_counters (n c : Nat) : counterNodes (leaderWord n c) = 0 := by
  induction n with
  | zero => simp [leaderWord, counterNodes, kernelLetter]
  | succ n ih => simpa [leaderWord, counterNodes, kernelLetter] using ih

theorem counterHeadDecrease : Targets.CounterHeadDecrease := by
  intro A B n m c e
  simp only [counterNodes_append, leaderWord_no_counters]
  simp [counterNodes, counterLetter]
  omega

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
