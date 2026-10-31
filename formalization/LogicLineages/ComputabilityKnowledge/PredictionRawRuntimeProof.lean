module

public import LogicLineages.ComputabilityKnowledge.PredictionRawRuntimeTargets
public import LogicLineages.ComputabilityKnowledge.PredictionRawTraceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawRuntimeProof
open PredictionRawMachine PredictionRawTrace PredictionRawRuntime PredictionRawRuntimeTargets

theorem terminalRunLengthUnique : TerminalRunLengthUnique := by
  intro k c d e n m p q h
  induction h generalizing e m q with
  | refl c =>
    intro hc h' he
    cases h' with
    | refl => rfl
    | step hs _ => simp [hc] at hs
  | @step c c' d n p hs hr ih =>
    intro hd h' he
    cases h' with
    | refl => simp [he] at hs
    | @step _ c'' _ m q hs' hr' =>
      have eq : c' = c'' := Option.some.inj (hs.symm.trans hs')
      subst c''
      exact congrArg (· + 1) (ih _ _ _ hd hr' he)

private theorem exact_run (n : Nat) :
    ∀ (k : Nat) (i : Label k), i.val = n → ∀ (state : Bool) (xs ys : List Bool),
    ∃ (fs : Bool) (pops : Nat),
      CostedRun k (runningCfg k i state xs ys)
        (terminalCfg k fs (xs.drop n) (decide (xs.length < n) :: ys))
        (min n xs.length + 1) pops := by
  induction n with
  | zero =>
    intro k i hi state xs ys
    have h := CostedRun.step (PredictionRawMachineProof.rawZeroTransition k i hi state xs ys)
      (CostedRun.refl (terminalCfg k state xs (false :: ys)))
    exact ⟨state, _, by simpa [hi] using h⟩
  | succ n ih =>
    intro k i hi state xs ys
    have hpos : 0 < i.val := by omega
    cases xs with
    | nil =>
      have h := CostedRun.step (PredictionRawMachineProof.rawEmptyTransition k i hpos state ys)
        (CostedRun.refl (terminalCfg k false [] (true :: ys)))
      exact ⟨false, _, by simpa using h⟩
    | cons a xs =>
      have hpred : (predecessor i).val = n := by simp [predecessor, hi]
      obtain ⟨fs, pops, hr⟩ := ih k (predecessor i) hpred true xs ys
      have h := CostedRun.step
        (PredictionRawMachineProof.rawNonemptyTransition k i hpos state a xs ys) hr
      exact ⟨fs, _, by simpa using h⟩

private theorem runtime_exists (k : Nat) (xs : List Bool) :
    HaltsAfter k xs (min k xs.length + 1) := by
  obtain ⟨fs, pops, hr⟩ := exact_run k k ⟨k, Nat.lt_succ_self k⟩ rfl false xs []
  exact ⟨_, pops, hr, PredictionRawMachineProof.rawTerminalTransition k fs _ _⟩

theorem exactInputRuntime : ExactInputRuntime := by
  intro k xs steps
  constructor
  · rintro ⟨d, p, hd, ht⟩
    obtain ⟨e, q, he, hu⟩ := runtime_exists k xs
    exact terminalRunLengthUnique k _ d e steps _ p q hd ht he hu
  · rintro rfl
    exact runtime_exists k xs

theorem exactWorstCaseRuntime : ExactWorstCaseRuntime := by
  intro k n
  refine ⟨?_, ?_, ?_⟩
  · intro xs hx
    apply (exactInputRuntime k xs _).2
    simp [worstCaseTransitions, hx]
  · refine ⟨List.replicate n false, by simp, ?_⟩
    apply (exactInputRuntime k _ _).2
    simp [worstCaseTransitions]
  · exact Nat.add_le_add_right (Nat.min_le_left k n) 1

end LogicLineages.ComputabilityKnowledge.PredictionRawRuntimeProof
