module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.LetterProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem compensatedGrowth : Targets.CompensatedGrowth := by
  intro D w
  induction w with
  | nil =>
      intro t _ hnon _
      obtain ⟨a,ha,_⟩ := hnon
      simp at ha
  | cons a w ih =>
      intro t ha hnon ht
      have ha' : LetterAllowed D a := ha a List.mem_cons_self
      have hw : WordAllowed D w := fun b hb => ha b (List.mem_cons_of_mem a hb)
      have hs := WordGuardCompletion.Proof.wordTailCorrect D (a::w) t ha ht
      refine ⟨hs.1,?_⟩
      change letterTail a+letterOffset a+wordTail w ≤ t at ht
      have hletter := WordGuardCompletion.Proof.letterTailCorrect D a t ha' (by omega)
      have hn : wordTail w ≤ letterValue a t := by omega
      change 2 ^ (t-(letterOffset a+wordOffset w)) ≤
        wordValue w (letterValue a t)+(letterOffset a+wordOffset w)
      by_cases hfirst : a.1 ≠ 0
      · have hg := (letterGrowth D a t ha' hfirst (by omega)).2
        have hr := (WordGuardCompletion.Proof.wordTailCorrect D w (letterValue a t) hw hn).2
        have hp : 2 ^ (t-(letterOffset a+wordOffset w)) ≤ 2 ^ t :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
        omega
      · have hrest : Nonlinear w := by
          obtain ⟨b,hb,hbnon⟩ := hnon
          rcases List.mem_cons.mp hb with hba | hbw
          · subst b
            exact (hfirst hbnon).elim
          · exact ⟨b,hbw,hbnon⟩
        have hg := (ih (letterValue a t) hw hrest hn).2
        have hexp : t-(letterOffset a+wordOffset w) ≤ letterValue a t-wordOffset w := by omega
        have hp : 2 ^ (t-(letterOffset a+wordOffset w)) ≤
            2 ^ (letterValue a t-wordOffset w) := Nat.pow_le_pow_right (by decide) hexp
        omega

theorem wordGrowth : Targets.WordGrowth := by
  intro D w t hw hnon ht
  have ht' : wordTail w+2*wordOffset w+2 ≤ t := ht
  have hg := compensatedGrowth D w t hw hnon (by omega)
  refine ⟨hg.1,?_⟩
  change 2 ^ (t-(wordOffset w+1)) ≤ wordValue w t
  have hexp : t-wordOffset w = (t-(wordOffset w+1))+1 := by omega
  have hsmall : wordOffset w ≤ t-(wordOffset w+1) := by omega
  have hpow : t-(wordOffset w+1) < 2 ^ (t-(wordOffset w+1)) := Nat.lt_two_pow_self
  have hdouble : 2 ^ (t-wordOffset w) = 2 * 2 ^ (t-(wordOffset w+1)) := by
    rw [hexp,pow_succ,Nat.mul_comm]
  rw [hdouble] at hg
  omega

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
