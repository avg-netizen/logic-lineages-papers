module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueTargets
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueProof
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel PredictionBinaryEpilogue PredictionBinaryEpilogueTargets

theorem exactThreeFuel : ExactThreeFuel := by
  intro b x hx
  have hh := (PredictionBinaryOutputLayoutProof.exactOutputCell b x hx).2
  have hb : workEq (x.Tape.move .right).head (rawSymbol true) = b := by
    rw [hh]
    cases b <;> rfl
  simp [run, initial, final, TM0.step, machine, hb]

theorem noEarlyReturn : NoEarlyReturn := by
  intro x
  rfl

theorem exactFinalOutput : ExactFinalOutput := by
  intro b x
  exact ⟨rfl, rfl⟩

end LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogueProof
