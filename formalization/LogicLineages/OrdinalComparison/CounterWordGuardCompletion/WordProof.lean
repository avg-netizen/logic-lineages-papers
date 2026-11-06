module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.ScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Signed shifts are interpreted in integers first; their nonnegative domains
justify the natural word extension, rather than hiding truncation. -/
private theorem shifted_counter_value (A : Word) (n c x : Nat) (j : Int)
    (hpos : 0 ≤ (sourceCount (n+3) c (wordValue A x) : Int)+j) :
    (wordValue (A ++ [counterLetter (n+3) c, shiftLetter j]) x : Int) =
      (sourceCount (n+3) c (wordValue A x) : Int)+j := by
  rw [WordAlgebraProof.wordValue_append]
  change (((sourceCount (n+3) c (wordValue A x) : Int)+j).toNat : Int) = _
  exact Int.toNat_of_nonneg hpos

private theorem shifted_counter_domain (A : Word) (n c x : Nat) (j : Int)
    (hA : WordDomain A x) (ht : c+(n+3)+1 ≤ wordValue A x)
    (hpos : 0 ≤ (sourceCount (n+3) c (wordValue A x) : Int)+j) :
    WordDomain (A ++ [counterLetter (n+3) c, shiftLetter j]) x := by
  apply (WordAlgebraProof.wordDomain_append A _ x).mpr
  refine ⟨hA,?_,hpos,trivial⟩
  change (4 : Nat) = 4 ∧ c ≤ Phi (wordValue A x)
  have hg := self_lt_Phi (wordValue A x)
  exact ⟨rfl,by omega⟩

theorem counterWordGuardCorrect : Targets.CounterWordGuardCorrect := by
  intro D A B hA hB n m c e j k hn hm x y hx hy
  have hAx : reachTail A (scalarTail n c e j k) ≤ x := (Nat.le_max_left _ _).trans hx
  have hBy : reachTail B (scalarTail m e c k j) ≤ y := (Nat.le_max_right _ _).trans hy
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A _ x hA hAx
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB hBy
  have hAl : leaderTail n c ≤ wordValue A x :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hAt.2)
  have hBl : leaderTail m e ≤ wordValue B y :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hBt.2)
  have hAb : c+(n+3)+1 ≤ wordValue A x :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hAt.2)
  have hBb : e+(m+3)+1 ≤ wordValue B y :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hBt.2)
  have hL := leaderWordCorrect D n c (wordValue A x) hn hAl
  have hR := leaderWordCorrect D m e (wordValue B y) hm hBl
  have hs := sourceShiftedCounterOrder n m c e (wordValue A x) (wordValue B y) j k hAt.2 hBt.2
  have hvL := shifted_counter_value A n c x j hs.1.le
  have hvR := shifted_counter_value B m e y k hs.2.1.le
  have hlt : wordValue (A ++ [counterLetter (n+3) c,shiftLetter j]) x <
      wordValue (B ++ [counterLetter (m+3) e,shiftLetter k]) y ↔
      CounterLexLT n m j k (wordValue (A++leaderWord n c) x)
        (wordValue (B++leaderWord m e) y) := by
    rw [WordAlgebraProof.wordValue_append A (leaderWord n c),
      WordAlgebraProof.wordValue_append B (leaderWord m e)]
    have hc : (wordValue (A ++ [counterLetter (n+3) c,shiftLetter j]) x : Int) <
        (wordValue (B ++ [counterLetter (m+3) e,shiftLetter k]) y : Int) ↔
        CounterLexLT n m j k (wordValue (leaderWord n c) (wordValue A x))
          (wordValue (leaderWord m e) (wordValue B y)) := by
      rw [hvL,hvR]
      exact hs.2.2.1
    exact_mod_cast hc
  have heq : wordValue (A ++ [counterLetter (n+3) c,shiftLetter j]) x =
      wordValue (B ++ [counterLetter (m+3) e,shiftLetter k]) y ↔
      wordValue (A++leaderWord n c) x = wordValue (B++leaderWord m e) y ∧ n = m ∧ j = k := by
    rw [WordAlgebraProof.wordValue_append A (leaderWord n c),
      WordAlgebraProof.wordValue_append B (leaderWord m e)]
    have hc : (wordValue (A ++ [counterLetter (n+3) c,shiftLetter j]) x : Int) =
        (wordValue (B ++ [counterLetter (m+3) e,shiftLetter k]) y : Int) ↔
        wordValue (leaderWord n c) (wordValue A x) =
          wordValue (leaderWord m e) (wordValue B y) ∧ n = m ∧ j = k := by
      rw [hvL,hvR]
      exact hs.2.2.2
    exact_mod_cast hc
  refine ⟨shifted_counter_domain A n c x j hAt.1 hAb hs.1.le,
    shifted_counter_domain B m e y k hBt.1 hBb hs.2.1.le,?_,?_,?_,?_,hlt,heq,?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hA a ha
    · exact hL.1 a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hB a ha
    · exact hR.1 a ha
  · exact (WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hAt.1,hL.2.1⟩
  · exact (WordAlgebraProof.wordDomain_append B _ y).mpr ⟨hBt.1,hR.2.1⟩
  · rw [le_iff_lt_or_eq,hlt,heq]

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
