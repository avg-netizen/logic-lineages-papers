module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineTargets
public import LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineProof
open Turing PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionValidatingMachine PredictionValidatingMachineTargets

private theorem loop_step (t : Tape TapeAlphabet) :
    TM0.step machine ⟨Label.loop, t⟩ = some ⟨Label.loop, t⟩ := by
  simp [TM0.step, machine, Tape.write_self]

theorem loopDivergence : LoopDivergence := by
  intro t
  apply Part.eq_none_iff.2
  intro y hy
  obtain ⟨hr, ht⟩ := StateTransition.mem_eval.1 hy
  have he : y = (⟨Label.loop, t⟩ : TM0.Cfg TapeAlphabet Label) := by
    clear hy ht
    induction hr with
    | refl => rfl
    | tail _ hs ih =>
      change TM0.step machine _ = some _ at hs
      rw [ih, loop_step] at hs
      exact (Option.some.inj hs).symm
  rw [he, loop_step] at ht
  cases ht

private theorem next_eval {x y : TM0.Cfg TapeAlphabet Label} (h : TM0.step machine x = some y) :
    StateTransition.eval (TM0.step machine) x = StateTransition.eval (TM0.step machine) y :=
  StateTransition.reaches_eval (Relation.ReflTransGen.single h)

private theorem stop_eval (t : Tape TapeAlphabet) :
    StateTransition.eval (TM0.step machine) ⟨Label.stop, t⟩ = Part.some ⟨Label.stop, t⟩ :=
  Part.eq_some_iff.2 (StateTransition.mem_eval.2 ⟨Relation.ReflTransGen.refl, rfl⟩)

private theorem second_eval (t : Tape TapeAlphabet) :
    StateTransition.eval (TM0.step machine) ⟨Label.second, t⟩ =
      if workEq t.head default then Part.some ⟨Label.stop, t.write (rawSymbol true)⟩ else Part.none := by
  cases h : workEq t.head default with
  | false =>
    have hs : TM0.step machine ⟨Label.second, t⟩ = some ⟨Label.loop, t⟩ := by
      simp [TM0.step, machine, h, Tape.write_self]
    rw [next_eval hs, loopDivergence t]
    simp [h]
  | true =>
    have hs : TM0.step machine ⟨Label.second, t⟩ = some ⟨Label.stop, t.write (rawSymbol true)⟩ := by
      simp [TM0.step, machine, h]
    rw [next_eval hs, stop_eval]
    simp [h]

private theorem first_eval (t : Tape TapeAlphabet) :
    StateTransition.eval (TM0.step machine) ⟨Label.first, t⟩ =
      if workEq t.head default then Part.some ⟨Label.stop, t.write (rawSymbol false)⟩
      else if workEq t.head (rawSymbol true) then
        StateTransition.eval (TM0.step machine) ⟨Label.second, t.move .right⟩ else Part.none := by
  cases h : workEq t.head default with
  | true =>
    have hs : TM0.step machine ⟨Label.first, t⟩ = some ⟨Label.stop, t.write (rawSymbol false)⟩ := by
      simp [TM0.step, machine, h]
    rw [next_eval hs, stop_eval]
    simp [h]
  | false =>
    cases hb : workEq t.head (rawSymbol true) with
    | false =>
      have hs : TM0.step machine ⟨Label.first, t⟩ = some ⟨Label.loop, t⟩ := by
        simp [TM0.step, machine, h, hb, Tape.write_self]
      rw [next_eval hs, loopDivergence t]
      simp [h, hb]
    | true =>
      have hs : TM0.step machine ⟨Label.first, t⟩ = some ⟨Label.second, t.move .right⟩ := by
        simp [TM0.step, machine, h, hb]
      rw [next_eval hs]
      simp [h, hb]

theorem exactValidatorEvaluation : ExactValidatorEvaluation := by
  intro t
  change StateTransition.eval (TM0.step machine) ⟨Label.check, t⟩ = _
  cases h : workEq t.head bottomSymbol with
  | false =>
    have hs : TM0.step machine ⟨Label.check, t⟩ = some ⟨Label.loop, t⟩ := by
      simp [TM0.step, machine, h, Tape.write_self]
    rw [next_eval hs, loopDivergence t]
    simp [PredictionNaturalOutputValidation.observe, h, Part.ofOption]
  | true =>
    have hs : TM0.step machine ⟨Label.check, t⟩ = some ⟨Label.first, t.move .right⟩ := by
      simp [TM0.step, machine, h]
    rw [next_eval hs, first_eval]
    cases h₁ : workEq (t.move .right).head default <;>
      cases h₂ : workEq (t.move .right).head (rawSymbol true) <;>
      cases h₃ : workEq ((t.move .right).move .right).head default <;>
      simp [PredictionNaturalOutputValidation.observe, finish, h, h₁, h₂, h₃, second_eval, Part.ofOption]

private theorem readout_finish (t : Tape TapeAlphabet) (b : Bool) : readout (finish t b) = b := by
  cases b <;> rfl

theorem sourceBinarySemantics : SourceBinarySemantics := by
  intro n x b hx
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).1 h
    rw [exactValidatorEvaluation x.Tape] at hd
    have ho := Part.mem_ofOption.mp hd
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [readout_finish] at he
    subst b
    exact (PredictionNaturalOutputValidationProof.exactBoundedObservation n x a hx).1 ha
  · intro hn
    have ha := (PredictionNaturalOutputValidationProof.exactBoundedObservation n x b hx).2 hn
    have hd : finish x.Tape b ∈ StateTransition.eval (TM0.step machine) (initial x.Tape) := by
      rw [exactValidatorEvaluation x.Tape, ha]
      exact Part.mem_some _
    exact (Part.mem_map_iff _).2 ⟨_, hd, readout_finish x.Tape b⟩

end LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineProof
