module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchProof
import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector GuardChildMeasureCompletion

theorem runTieBound : RunnerTargets.RunTieBound := by
  intro p n
  induction n with
  | zero => change 1 ≤ 2; omega
  | succ n ih =>
      rw [run_succ]
      cases hsel : selectWords (run p n).1.1 (run p n).1.2 with
      | none => simpa only [step,hsel] using ih
      | some q =>
          have hb := ComparisonProof.liftTie_bound (run p n).2.2
            (dispatchTie (run p n).1.1 (run p n).1.2) ih
            (DispatchProof.dispatchTieBound (run p n).1.1 (run p n).1.2)
          simpa only [step,hsel] using hb

theorem traceDomains : RunnerTargets.TraceDomains := by
  intro D p hp n x y hx hy k hkn
  have hpaid := (run_bounds p k n hkn).2
  have hw := (admissionCorrect D (run p k).1).mp (runAdmission D p hp k)
  have hleft : wordTail (run p k).1.1 ≤ paidTail (run p k) :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hright : wordTail (run p k).1.2 ≤ paidTail (run p k) :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact ⟨(WordGuardCompletion.Proof.wordTailCorrect D (run p k).1.1 x hw.1
      (hleft.trans (hpaid.trans hx))).1,
    (WordGuardCompletion.Proof.wordTailCorrect D (run p k).1.2 y hw.2
      (hright.trans (hpaid.trans hy))).1⟩

theorem accumulatedComparison : RunnerTargets.AccumulatedComparison := by
  intro D p hp n
  induction n with
  | zero =>
      intro x y _ _
      change orderNat (wordValue p.1 x) (wordValue p.2 y) =
        liftTie 1 (orderNat (wordValue p.1 x) (wordValue p.2 y))
      exact (ComparisonProof.liftTie_one _).symm
  | succ n ih =>
      intro x y hx hy
      have hbound := (run_bounds p n (n+1) (by omega)).1
      have hprevious := ih x y (hbound.trans hx) (hbound.trans hy)
      cases hsel : selectWords (run p n).1.1 (run p n).1.2 with
      | none =>
          have hstay : run p (n+1) = run p n := by
            rw [run_succ]
            simp only [step,hsel]
          simpa only [hstay] using hprevious
      | some q =>
          have hw := (admissionCorrect D (run p n).1).mp (runAdmission D p hp n)
          have hlocal := dispatchCoverage p n (n+1) q (by omega) hsel
          obtain ⟨_,_,_,_,_,_,horder⟩ := DispatchProof.dispatchCorrect D
            (run p n).1.1 (run p n).1.2 q hw.1 hw.2 hsel x y
            (hlocal.trans hx) (hlocal.trans hy)
          calc
            orderNat (wordValue p.1 x) (wordValue p.2 y) =
                liftTie (run p n).2.2
                  (orderNat (wordValue (run p n).1.1 x) (wordValue (run p n).1.2 y)) := hprevious
            _ = liftTie (liftTie (run p n).2.2 (dispatchTie (run p n).1.1 (run p n).1.2))
                (orderNat (wordValue q.2.2.1 x) (wordValue q.2.2.2 y)) := by
              rw [horder,ComparisonProof.liftTie_assoc]
            _ = liftTie (run p (n+1)).2.2
                (orderNat (wordValue (run p (n+1)).1.1 x) (wordValue (run p (n+1)).1.2 y)) := by
              rw [run_succ]
              simp only [step,hsel]

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
