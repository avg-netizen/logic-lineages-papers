module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassProof
open PredictionTapeObservation PredictionTapeRuntime PredictionTapeRuntimeClass PredictionTapeRuntimeClassTargets

private theorem bounded_iff_success (code : Nat) (he : TotalBinary code) (budget : Nat) (xs : List Bool) :
    boundedMove code budget xs = some (policy code he xs) ↔ Successful code xs (budget - 1) := by
  constructor
  · intro h
    obtain ⟨v, hv, _⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨d, hd, _⟩ := Option.map_eq_some_iff.mp hv
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    have ho : observe code budget xs = some (d.2.1 % PredictionFiniteAlphabet.width (PredictionFiniteAlphabet.decodeTable code)) :=
      congrArg (Option.map (fun z : PredictionFiniteAlphabet.Raw => z.2.1 % PredictionFiniteAlphabet.width (PredictionFiniteAlphabet.decodeTable code))) hd
    have heq := PredictionTapeObservationProof.observationUniqueOnTotal code he budget xs _ ho
    unfold boundedMove
    rw [ho]
    exact (PredictionUniformBinaryCompilerProof.physicalBinaryReadout _ _).2 heq

theorem exactAvailabilityCalibration : ExactAvailabilityCalibration := by
  intro e he b
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => (strictBudgetCalibration e n (b n)).2 ?_⟩
    intro xs hx
    exact (bounded_iff_success e he (b n) xs).1 (hN n hn xs hx)
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn xs hx => (bounded_iff_success e he (b n) xs).2 ?_⟩
    exact (strictBudgetCalibration e n (b n)).1 (hN n hn) xs hx

theorem effectiveEvaderCodes : EffectiveEvaderCodes :=
  PredictionAlphabetEmbeddingProof.effectiveEmbedding.comp PredictionTapeCodeProof.effectiveCodeFamily

private theorem evader_width (k : Nat) :
    PredictionFiniteAlphabet.width (PredictionFiniteAlphabet.decodeTable (evaderCode k)) = 3 := by
  simp [evaderCode, PredictionAlphabetEmbedding.liftCode, PredictionFiniteAlphabet.decodeTable,
    Encodable.encodek, PredictionAlphabetEmbedding.liftTable, PredictionFiniteAlphabet.width]

private theorem evader_observation (k : Nat) (xs : List Bool) :
    boundedMove (evaderCode k) (k + 3) xs = some (decide (xs.length < k)) := by
  obtain ⟨d, hd⟩ := (PredictionAlphabetEmbeddingProof.exactEvaderRuntime k xs (k + 2)).2
    (Nat.add_le_add_right (Nat.min_le_left k xs.length) 2)
  have hv := PredictionAlphabetEmbeddingProof.exactEvaderOutput k xs (k + 2) d hd
  change PredictionFiniteAlphabet.simulate (evaderCode k) (k + 2) xs = some d at hd
  have hf : k + 3 - 1 = k + 2 := by omega
  unfold boundedMove observe
  rw [hf, hd]
  simp only [Option.map_some, Option.bind_some]
  rw [evader_width, hv]
  by_cases h : xs.length < k <;> simp [h, PredictionUniformBinaryCompiler.readBit]

theorem exactEvaderPolicy : ExactEvaderPolicy := by
  intro k
  have ht : TotalBinary (evaderCode k) := by
    intro xs
    exact ⟨decide (xs.length < k), (PredictionTapeObservationProof.exactBinarySemantics _ _ _).2
      ⟨k + 3, evader_observation k xs⟩⟩
  refine ⟨ht, ?_⟩
  funext xs
  have hknown := (PredictionTapeObservationProof.exactBinarySemantics _ _ _).2
    ⟨k + 3, evader_observation k xs⟩
  exact Part.mem_unique (Classical.choose_spec (ht xs)) hknown

private theorem worst_unique {code n s t : Nat} (hs : WorstTime code n s) (ht : WorstTime code n t) : s = t := by
  have hs' := (worstTimeThreshold code n s).1 hs
  have ht' := (worstTimeThreshold code n t).1 ht
  exact Nat.le_antisymm ((hs' t).1 ((ht' t).2 le_rfl)) ((ht' s).1 ((hs' s).2 le_rfl))

theorem exactEvaderMembership : ExactEvaderMembership := by
  intro k b
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨t, ht, hb⟩ := hN n hn
    rwa [worst_unique ht (exactEvaderWorstTime k n)] at hb
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn => ⟨min k n + 2, exactEvaderWorstTime k n, hN n hn⟩⟩

end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassProof
