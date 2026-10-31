module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationTargets
public import LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeObservationProof
open Turing PredictionFiniteAlphabet PredictionTapeObservation PredictionTapeObservationTargets

private theorem pr_read : Primrec PredictionUniformBinaryCompiler.readBit :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const (some false))
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const (some true)) (Primrec.const none))

theorem effectiveObservation : EffectiveObservation := by
  have hf : Primrec (fun z : Nat × Nat × List Bool => simulate z.1 (z.2.1 - 1) z.2.2) :=
    PredictionFiniteAlphabetProof.effectiveBoundedSimulation.comp
      (Primrec.fst.pair ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).pair
        (Primrec.snd.comp Primrec.snd)))
  have hw : Primrec (fun z : Nat × Nat × List Bool => width (decodeTable z.1)) :=
    (Primrec.nat_add.comp (Primrec.fst.comp
      (PredictionFiniteAlphabetProof.effectiveDecoding.1.comp Primrec.fst)) (Primrec.const 3))
  have ho : Primrec (fun z : Nat × Nat × List Bool => observe z.1 z.2.1 z.2.2) :=
    Primrec.option_map hf (Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (hw.comp Primrec.fst)).to₂
  exact ⟨ho, Primrec.option_bind ho (pr_read.comp Primrec.snd).to₂⟩

theorem soundObservation : SoundObservation := by
  intro code budget xs v hv
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hv
  have hy := (PredictionFiniteAlphabetEvaluation.boundedEvaluation (decodeTable code)
    (initial (decodeTable code) xs) (toCfg (decodeTable code) d)).1 ⟨budget - 1, d, hd, rfl⟩
  exact Part.mem_map _ hy

private theorem binary_eval_mem (code : Nat) (xs : List Bool) (b : Bool) :
    b ∈ PredictionUniformBinaryCompiler.binaryEval code xs ↔
      ∃ y, y ∈ StateTransition.eval (TM0.step (machine (decodeTable code)))
        (toCfg (decodeTable code) (initial (decodeTable code) xs)) ∧
        y.Tape.head.val = inputSymbol b := by
  change (b ∈ Part.bind _ _) ↔ _
  simp only [Part.mem_bind_iff, Part.mem_ofOption, Option.mem_def]
  apply exists_congr
  intro y
  exact and_congr_right (fun _ => PredictionUniformBinaryCompilerProof.physicalBinaryReadout _ b)

theorem exactBinarySemantics : ExactBinarySemantics := by
  intro code xs b
  rw [binary_eval_mem, ← PredictionFiniteAlphabetEvaluation.binaryOutputEvaluation code xs b]
  constructor
  · rintro ⟨fuel, d, hd, hb⟩
    refine ⟨fuel + 1, ?_⟩
    have hr := (PredictionUniformBinaryCompilerProof.physicalBinaryReadout _ b).2 hb
    simp only [boundedMove, observe, Nat.add_sub_cancel, hd, Option.map_some, Option.bind_some]
    exact hr
  · rintro ⟨budget, hb⟩
    obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hv
    exact ⟨budget - 1, d, hd, (PredictionUniformBinaryCompilerProof.physicalBinaryReadout _ b).1 hr⟩

theorem observationUniqueOnTotal : ObservationUniqueOnTotal := by
  intro code h budget xs v hv
  have hb : policy code h xs ∈ PredictionUniformBinaryCompiler.binaryEval code xs := Classical.choose_spec (h xs)
  obtain ⟨y, hy, he⟩ := (binary_eval_mem code xs (policy code h xs)).1 hb
  have hn : y.Tape.head.val ∈ naturalEval code xs := Part.mem_map _ hy
  exact (Part.mem_unique (soundObservation code budget xs v hv) hn).trans he

end LogicLineages.ComputabilityKnowledge.PredictionTapeObservationProof
