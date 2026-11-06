module
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.ScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion

private theorem counter_value (A : Word) (n c x : Nat) (j : Int)
    (hpos : 0 ≤ (sourceCount (n+3) c (wordValue A x) : Int)+j) :
    (wordValue (A ++ [counterLetter (n+3) c, shiftLetter j]) x : Int) =
      (sourceCount (n+3) c (wordValue A x) : Int)+j := by
  rw [WordAlgebraProof.wordValue_append]
  change (((sourceCount (n+3) c (wordValue A x) : Int)+j).toNat : Int) = _
  exact Int.toNat_of_nonneg hpos

private theorem phi_value (B : Word) (y : Nat) (k : Int)
    (hpos : 0 ≤ (Phi (wordValue B y) : Int)+k) :
    (wordValue (B ++ [phiLetter, shiftLetter k]) y : Int) = (Phi (wordValue B y) : Int)+k := by
  rw [WordAlgebraProof.wordValue_append]
  change (((Phi (wordValue B y) : Int)+k).toNat : Int) = _
  exact Int.toNat_of_nonneg hpos

theorem counterPhiWordGuardCorrect : Targets.CounterPhiWordGuardCorrect := by
  intro D A B hA hB n c j k hn x y hx hy
  have hAx : reachTail A (counterTail n c (j.natAbs+k.natAbs)) ≤ x := (Nat.le_max_left _ _).trans hx
  have hBy : reachTail B (rangeTail (j.natAbs+k.natAbs)) ≤ y := (Nat.le_max_right _ _).trans hy
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A _ x hA hAx
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB hBy
  have hAl : CounterWordGuardCompletion.leaderTail n c ≤ wordValue A x :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hAt.2)
  have hAb' : c+(n+3)+1+(j.natAbs+k.natAbs) ≤ wordValue A x :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hAt.2)
  have hL := CounterWordGuardCompletion.Proof.leaderWordCorrect D n c (wordValue A x) hn hAl
  have hs := sourceShiftedCounterPhiOrder n c (wordValue A x) (wordValue B y) j k hAt.2 hBt.2
  have hvL := counter_value A n c x j hs.1.le
  have hvR := phi_value B y k hs.2.1.le
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (WordAlgebraProof.wordDomain_append A _ x).mpr
    refine ⟨hAt.1,?_,hs.1.le,trivial⟩
    change (4 : Nat) = 4 ∧ c ≤ Phi (wordValue A x)
    have hg := self_lt_Phi (wordValue A x)
    exact ⟨rfl,by omega⟩
  · apply (WordAlgebraProof.wordDomain_append B _ y).mpr
    exact ⟨hBt.1,trivial,hs.2.1.le,trivial⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hA a ha
    · exact hL.1 a ha
  · exact (WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hAt.1,hL.2.1⟩
  · have h := hs.2.2.1
    rw [←hvL,←hvR,←WordAlgebraProof.wordValue_append A (leaderWord n c) x] at h
    exact_mod_cast h
  · have h := hs.2.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.2.1
    rw [←hvL,←hvR,←WordAlgebraProof.wordValue_append A (leaderWord n c) x] at h
    exact_mod_cast h
  · have h := hs.2.2.2.2.2
    rw [←hvL,←hvR,←WordAlgebraProof.wordValue_append A (leaderWord n c) x] at h
    exact_mod_cast h

private theorem counterNodes_append (A B : Word) :
    counterNodes (A++B) = counterNodes A+counterNodes B := by
  simp [counterNodes, List.filter_append]

private theorem leader_no_counters (n c : Nat) : counterNodes (leaderWord n c) = 0 := by
  induction n with
  | zero => simp [leaderWord, counterNodes, kernelLetter]
  | succ n ih => simpa [leaderWord, counterNodes, kernelLetter] using ih

theorem counterHeadDecrease : Targets.CounterHeadDecrease := by
  intro A B n c
  simp only [counterNodes_append,leader_no_counters]
  simp [counterNodes,counterLetter,phiLetter]
  omega

end LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
