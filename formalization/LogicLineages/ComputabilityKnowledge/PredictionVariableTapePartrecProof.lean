module
public import LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecProof
open PredictionVariableTapePartrec PredictionVariableTapePartrecTargets

theorem effectiveBinaryObservation : EffectiveBinaryObservation :=
  Primrec.option_map PredictionTapeObservationProof.effectiveObservation.2
    ((Primrec.dom_bool Bool.toNat).comp Primrec.snd).to₂

private theorem observation_semantics (code : Nat) (xs : List Bool) (v : Nat) :
    (∃ fuel, observation code fuel xs = some v) ↔ Produces code xs v := by
  constructor
  · rintro ⟨fuel, hf⟩
    obtain ⟨b, hb, hv⟩ := Option.map_eq_some_iff.mp hf
    exact ⟨b, (PredictionTapeObservationProof.exactBinarySemantics code xs b).2 ⟨fuel, hb⟩, hv.symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨fuel, hf⟩ := (PredictionTapeObservationProof.exactBinarySemantics code xs b).1 hb
    exact ⟨fuel, congrArg (Option.map Bool.toNat) hf⟩

private theorem move_mono (code : Nat) (xs : List Bool) {m n : Nat} {b : Bool}
    (hmn : m ≤ n) (h : PredictionTapeObservation.boundedMove code m xs = some b) :
    PredictionTapeObservation.boundedMove code n xs = some b := by
  obtain ⟨v, hv, hb⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d, hd, hvd⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨t, ht, hr, hh⟩ := (PredictionFiniteAlphabetProof.exactBoundedSimulation _ _ _ _).1 hd
  have hd' : PredictionFiniteAlphabet.simulate code (n - 1) xs = some d :=
    (PredictionFiniteAlphabetProof.exactBoundedSimulation _ _ _ _).2
      ⟨t, lt_of_lt_of_le ht (Nat.sub_le_sub_right hmn 1), hr, hh⟩
  unfold PredictionTapeObservation.boundedMove PredictionTapeObservation.observe
  rw [hd']
  simp only [Option.map_some, Option.bind_some]
  rw [hvd]
  exact hb

private theorem observation_mono (code : Nat) (xs : List Bool) {v m n : Nat}
    (hmn : m ≤ n) (h : v ∈ observation code m xs) : v ∈ observation code n xs := by
  obtain ⟨b, hb, hv⟩ := Option.map_eq_some_iff.mp (Option.mem_def.mp h)
  exact Option.mem_def.mpr (Option.map_eq_some_iff.mpr ⟨b, move_mono code xs hmn hb, hv⟩)

private theorem searched_semantics (code : Nat) (xs : List Bool) (v : Nat) :
    v ∈ Nat.rfindOpt (fun fuel => observation code fuel xs) ↔ Produces code xs v := by
  rw [Nat.rfindOpt_mono (fun hmn hv => observation_mono code xs hmn hv)]
  exact observation_semantics code xs v

private def decoded (n : Nat) : List Bool :=
  (Encodable.decode (α := List Bool) n.unpair.2).getD []

private def obs (n fuel : Nat) : Option Nat := observation n.unpair.1 fuel (decoded n)

private theorem decoded_computable : Computable decoded :=
  (Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])).to_comp

private theorem argument_computable :
    Computable (fun z : Nat × Nat => (z.1.unpair.1, z.2, decoded z.1)) :=
  (Computable.fst.comp (Computable.unpair.comp Computable.fst)).pair
    (Computable.snd.pair (decoded_computable.comp Computable.fst))

private theorem observation_computable : Computable₂ obs := by
  change Computable (fun z : Nat × Nat => observation z.1.unpair.1 z.2 (decoded z.1))
  have h : Computable (fun z : Nat × Nat × List Bool => observation z.1 z.2.1 z.2.2) :=
    effectiveBinaryObservation.to_comp
  exact Computable.comp
    (f := fun z : Nat × Nat × List Bool => observation z.1 z.2.1 z.2.2)
    (g := fun z : Nat × Nat => (z.1.unpair.1, z.2, decoded z.1)) h argument_computable

private theorem searched_partrec : Partrec (fun n => Nat.rfindOpt (obs n)) :=
  Partrec.rfindOpt observation_computable

private theorem obs_encode (code : Nat) (xs : List Bool) :
    obs (Nat.pair code (Encodable.encode xs)) = fun fuel => observation code fuel xs := by
  funext fuel
  simp only [obs, decoded, Nat.unpair_pair, Encodable.encodek, Option.getD_some]

theorem uniformBinaryCompiler : UniformBinaryCompiler := by
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp searched_partrec)
  refine ⟨u, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id, ?_⟩
  intro code xs v
  rw [compile, Nat.Partrec.Code.eval_curry, hu]
  change v ∈ Nat.rfindOpt (obs (Nat.pair code (Encodable.encode xs))) ↔ _
  rw [obs_encode]
  exact searched_semantics code xs v

theorem totalBinaryCorrespondence : TotalBinaryCorrespondence := by
  obtain ⟨u, hu, hs⟩ := uniformBinaryCompiler
  refine ⟨u, hu, hs, ?_⟩
  intro code
  constructor
  · intro h xs
    obtain ⟨b, hb⟩ := h xs
    obtain ⟨a, ha, _⟩ := (hs code xs (PredictionLearning.bitValue b)).1 hb
    exact ⟨a, ha⟩
  · intro h xs
    obtain ⟨b, hb⟩ := h xs
    exact ⟨b, (hs code xs (PredictionLearning.bitValue b)).2 ⟨b, hb, by cases b <;> rfl⟩⟩

end LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecProof
