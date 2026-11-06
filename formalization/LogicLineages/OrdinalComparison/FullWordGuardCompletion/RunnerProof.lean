module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerTargets
import LogicLineages.OrdinalComparison.CanonicalGuardSelector.BridgeProof
import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.MeasureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector GuardChildMeasureCompletion

theorem admittedLetter_correct (D : Nat) (a : Letter) :
    admittedLetter D a = true ↔ LetterAllowed D a := by
  by_cases h : a.1 ≤ 2
  · simp [admittedLetter,LetterAllowed,h]
  · simp [admittedLetter,LetterAllowed,h,Bool.and_eq_true,Bool.or_eq_true,
      beq_iff_eq,and_assoc]

theorem admittedWord_correct (D : Nat) (w : Word) :
    admittedWord D w = true ↔ WordAllowed D w := by
  simp only [admittedWord,List.all_eq_true,admittedLetter_correct,WordAllowed]

theorem admissionCorrect : RunnerTargets.AdmissionCorrect := by
  intro D p
  simp only [admitted,Bool.and_eq_true,admittedWord_correct]

theorem run_zero (p : WordPair) : run p 0 = initial p := rfl

theorem run_succ (p : WordPair) (n : Nat) : run p (n+1) = step (run p n) := by
  exact Function.iterate_succ_apply' step n (initial p)

theorem runEquations : RunnerTargets.RunEquations := by
  intro p
  exact ⟨run_zero p,run_succ p⟩

theorem stepBounds (s : State) :
    s.2.1 ≤ (step s).2.1 ∧ paidTail s ≤ paidTail (step s) := by
  cases h : selectWords s.1.1 s.1.2 with
  | none => simp only [step,h]; exact ⟨le_rfl,le_rfl⟩
  | some q =>
      simp only [step,h]
      refine ⟨Nat.le_max_left _ _,?_⟩
      have hlocal : max (wordTail s.1.1) (wordTail s.1.2) ≤
          dispatchTail s.1.1 s.1.2 := by
        unfold dispatchTail
        omega
      unfold paidTail
      dsimp only
      omega

theorem run_bounds (p : WordPair) (m n : Nat) (hmn : m ≤ n) :
    (run p m).2.1 ≤ (run p n).2.1 ∧ paidTail (run p m) ≤ paidTail (run p n) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact ⟨le_rfl,le_rfl⟩
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        exact ⟨le_rfl,le_rfl⟩
      · have hprev := ih m (by omega : m ≤ n)
        have hnext := stepBounds (run p n)
        rw [← run_succ] at hnext
        exact ⟨hprev.1.trans hnext.1,hprev.2.trans hnext.2⟩

theorem runBounds : RunnerTargets.RunBounds := ⟨stepBounds,run_bounds⟩

theorem dispatchCoverage : RunnerTargets.DispatchCoverage := by
  intro p m n q hmn hsel
  have hlocal : dispatchTail (run p m).1.1 (run p m).1.2 ≤ (run p (m+1)).2.1 := by
    rw [run_succ]
    simp only [step,hsel]
    exact Nat.le_max_right _ _
  exact hlocal.trans (run_bounds p (m+1) n (by omega)).1

theorem runAdmission : RunnerTargets.RunAdmission := by
  intro D p hp n
  induction n with
  | zero => simpa only [run_zero,initial] using hp
  | succ n ih =>
      rw [run_succ]
      cases hsel : selectWords (run p n).1.1 (run p n).1.2 with
      | none => simpa only [step,hsel] using ih
      | some q =>
          have hw := (admissionCorrect D (run p n).1).mp ih
          have hchild := CanonicalGuardSelector.Proof.selectedChildCorrect D
            (run p n).1.1 (run p n).1.2 q hw.1 hw.2 hsel
          have hnext := (admissionCorrect D q.2.2).mpr ⟨hchild.2.2.1,hchild.2.2.2⟩
          simpa only [step,hsel] using hnext

theorem terminalStability : RunnerTargets.TerminalStability := by
  intro p n hterminal k
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
      rw [Nat.add_succ,run_succ,ih]
      simp only [step,hterminal]

/-- Well-founded recursion follows the actual selected pair, while the
numeric cutoff and equality tie may be arbitrary accumulated values. -/
private theorem reachesTerminal (D : Nat) (p : WordPair) :
    WordAllowed D p.1 → WordAllowed D p.2 → ∀ cutoff tie : Nat,
    ∃ n : Nat,
      selectWords ((step^[n]) (p,cutoff,tie)).1.1
        ((step^[n]) (p,cutoff,tie)).1.2 = none := by
  refine (GuardChildMeasureCompletion.Proof.measureWellFounded D).induction
    (C := fun q : WordPair =>
      WordAllowed D q.1 → WordAllowed D q.2 → ∀ cutoff tie : Nat,
      ∃ n : Nat, selectWords ((step^[n]) (q,cutoff,tie)).1.1
        ((step^[n]) (q,cutoff,tie)).1.2 = none) p ?_
  intro p ih hA hB cutoff tie
  cases hsel : selectWords p.1 p.2 with
  | none =>
      refine ⟨0,?_⟩
      exact hsel
  | some q =>
      have hchild := CanonicalGuardSelector.Proof.selectedChildCorrect D p.1 p.2 q hA hB hsel
      obtain ⟨n,hn⟩ := ih q.2.2 hchild.2.1 hchild.2.2.1 hchild.2.2.2
        (max cutoff (dispatchTail p.1 p.2)) (liftTie tie (dispatchTie p.1 p.2))
      have hstep : step (p,cutoff,tie) =
          (q.2.2,max cutoff (dispatchTail p.1 p.2),liftTie tie (dispatchTie p.1 p.2)) := by
        simp only [step,hsel]
      refine ⟨n+1,?_⟩
      simpa only [Function.iterate_succ_apply,hstep] using hn

theorem runnerTerminates : RunnerTargets.RunnerTerminates := by
  intro D p
  cases h : admitted D p with
  | false => exact ⟨0,by simp only [stopped,h,Bool.not_false,Bool.true_or]⟩
  | true =>
      have hw := (admissionCorrect D p).mp h
      obtain ⟨n,hn⟩ := reachesTerminal D p hw.1 hw.2 0 1
      have hterminal : selectWords (run p n).1.1 (run p n).1.2 = none := hn
      exact ⟨n,by simp only [stopped,h,hterminal,Bool.not_true,Bool.false_or,Option.isNone_none]⟩

theorem leastFuel_eq (D : Nat) (p : WordPair) :
    leastFuel D p = Nat.find (runnerTerminates D p) := by
  unfold leastFuel
  rw [dif_pos (runnerTerminates D p)]

theorem leastFuelCorrect : RunnerTargets.LeastFuelCorrect := by
  intro D p
  have hstop : stopped D p (leastFuel D p) = true := by
    rw [leastFuel_eq]
    exact Nat.find_spec (runnerTerminates D p)
  refine ⟨hstop,?_,?_,?_⟩
  · intro n hn
    have hminimal := Nat.find_min (runnerTerminates D p) (by rwa [← leastFuel_eq])
    cases hb : stopped D p n with
    | false => rfl
    | true => exact False.elim (hminimal hb)
  · intro hinvalid
    have hzero : stopped D p 0 = true := by
      simp only [stopped,hinvalid,Bool.not_false,Bool.true_or]
    have hle : leastFuel D p ≤ 0 := by
      rw [leastFuel_eq]
      exact Nat.find_min' (runnerTerminates D p) hzero
    exact Nat.eq_zero_of_le_zero hle
  · intro hadmitted
    have hterminal :
        selectWords (run p (leastFuel D p)).1.1 (run p (leastFuel D p)).1.2 = none := by
      cases hs : selectWords (run p (leastFuel D p)).1.1 (run p (leastFuel D p)).1.2 with
      | none => rfl
      | some q => simp only [stopped,hadmitted,hs,Bool.not_true,Bool.false_or,
          Option.isNone_some,Bool.false_eq_true] at hstop
    refine ⟨hterminal,?_⟩
    intro n hn
    simpa only [Nat.add_sub_of_le hn] using
      terminalStability p (leastFuel D p) hterminal (n-leastFuel D p)

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
