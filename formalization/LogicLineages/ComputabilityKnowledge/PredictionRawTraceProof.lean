module

public import LogicLineages.ComputabilityKnowledge.PredictionRawTraceTargets
public import LogicLineages.ComputabilityKnowledge.PredictionRawMachineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawTraceProof
open PredictionRawMachine PredictionRawTrace PredictionRawTraceTargets

theorem rawBlockPopBound : RawBlockPopBound := by
  intro k i
  by_cases h : i.val = 0 <;> simp [evaderStmt, h, inputPopBound]

private theorem running_cost (k : Nat) (i : Label k) (state : Bool) (xs ys : List Bool) :
    configurationPopBound (runningCfg k i state xs ys) = if i.val = 0 then 0 else 1 :=
  rawBlockPopBound k i

private theorem run_bound (n : Nat) :
    ∀ (k : Nat) (i : Label k), i.val = n → ∀ (state : Bool) (xs ys : List Bool),
    ∃ (finalState : Bool) (steps pops : Nat), steps ≤ n + 1 ∧ pops ≤ n ∧
      CostedRun k (runningCfg k i state xs ys)
        (terminalCfg k finalState (xs.drop n) (decide (xs.length < n) :: ys)) steps pops := by
  induction n with
  | zero =>
    intro k i hi state xs ys
    refine ⟨state, 1, 0, by omega, by omega, ?_⟩
    have h := CostedRun.step (PredictionRawMachineProof.rawZeroTransition k i hi state xs ys)
      (CostedRun.refl (terminalCfg k state xs (false :: ys)))
    simpa [running_cost, hi] using h
  | succ n ih =>
    intro k i hi state xs ys
    have hpos : 0 < i.val := by omega
    cases xs with
    | nil =>
      refine ⟨false, 1, 1, by omega, by omega, ?_⟩
      have h := CostedRun.step (PredictionRawMachineProof.rawEmptyTransition k i hpos state ys)
        (CostedRun.refl (terminalCfg k false [] (true :: ys)))
      simpa [running_cost, hi] using h
    | cons a xs =>
      have hpred : (predecessor i).val = n := by simp [predecessor, hi]
      obtain ⟨fs, steps, pops, hs, hp, hr⟩ := ih k (predecessor i) hpred true xs ys
      refine ⟨fs, steps + 1, 1 + pops, by omega, by omega, ?_⟩
      have h := CostedRun.step
        (PredictionRawMachineProof.rawNonemptyTransition k i hpos state a xs ys) hr
      simpa [running_cost, hi] using h

theorem rawRunCorrect : RawRunCorrect := by
  intro k i state xs ys
  exact run_bound i.val k i rfl state xs ys

theorem rawInitialOutput : RawInitialOutput := by
  intro k xs
  obtain ⟨fs, steps, pops, hs, hp, hr⟩ := rawRunCorrect k ⟨k, Nat.lt_succ_self k⟩ false xs []
  refine ⟨terminalCfg k fs (xs.drop k) [decide (xs.length < k)], steps, pops, hs, hp, hr, ?_⟩
  exact ⟨PredictionRawMachineProof.rawTerminalTransition k fs _ _, rfl, rfl⟩

end LogicLineages.ComputabilityKnowledge.PredictionRawTraceProof
