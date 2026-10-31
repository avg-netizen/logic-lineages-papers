module
public import LogicLineages.ComputabilityKnowledge.PredictionTapePartrecTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapePartrecProof
open PredictionTapeTable PredictionLearning PredictionTapePartrec PredictionTapePartrecTargets

theorem effectiveObservation : EffectiveObservation := by
  have hb : Primrec bitValue := Primrec.dom_bool bitValue
  have ho : Primrec (fun d : Raw => d.2.1.map bitValue) :=
    Primrec.option_map (Primrec.fst.comp Primrec.snd) (hb.comp Primrec.snd).to₂
  exact Primrec.option_bind PredictionTapeTableProof.effectiveBoundedSimulation
    (ho.comp Primrec.snd).to₂

private theorem observation_iff (code fuel : Nat) (xs : List Bool) (v : Nat) :
    observation code fuel xs = some v ↔
      ∃ (d : Raw) (b : Bool), simulate code fuel xs = some d ∧
        d.2.1 = some b ∧ bitValue b = v := by
  simp [observation, Option.bind_eq_some_iff, Option.map_eq_some_iff]

theorem operationalObservation : OperationalObservation := by
  intro code xs v
  constructor
  · rintro ⟨fuel, hf⟩
    obtain ⟨d, b, hd, hb, hv⟩ := (observation_iff code fuel xs v).1 hf
    obtain ⟨n, _, hr, hh⟩ := (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).1 hd
    exact ⟨n, d, b, hr, hh, hb, hv.symm⟩
  · rintro ⟨n, d, b, hr, hh, hb, hv⟩
    refine ⟨n + 1, (observation_iff code (n + 1) xs v).2 ⟨d, b, ?_, hb, hv.symm⟩⟩
    exact (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).2
      ⟨n, by omega, hr, hh⟩

private theorem observation_mono (code : Nat) (xs : List Bool)
    {v m n : Nat} (hmn : m ≤ n) (h : v ∈ observation code m xs) :
    v ∈ observation code n xs := by
  obtain ⟨d, b, hd, hb, hv⟩ := (observation_iff code m xs v).1 h
  obtain ⟨t, ht, hr, hh⟩ := (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).1 hd
  exact (observation_iff code n xs v).2 ⟨d, b,
    (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).2
      ⟨t, by omega, hr, hh⟩, hb, hv⟩

private theorem searched_semantics (code : Nat) (xs : List Bool) (v : Nat) :
    v ∈ Nat.rfindOpt (fun fuel => observation code fuel xs) ↔ Produces code xs v := by
  rw [Nat.rfindOpt_mono (fun hmn hv => observation_mono code xs hmn hv)]
  exact operationalObservation code xs v

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
    effectiveObservation.to_comp
  exact Computable.comp
    (f := fun z : Nat × Nat × List Bool => observation z.1 z.2.1 z.2.2)
    (g := fun z : Nat × Nat => (z.1.unpair.1, z.2, decoded z.1))
    h argument_computable

private theorem searched_partrec : Partrec (fun n => Nat.rfindOpt (obs n)) :=
  Partrec.rfindOpt observation_computable

private theorem obs_encode (code : Nat) (xs : List Bool) :
    obs (Nat.pair code (Encodable.encode xs)) = fun fuel => observation code fuel xs := by
  funext fuel
  simp only [obs, decoded, Nat.unpair_pair, Encodable.encodek, Option.getD_some]

theorem uniformOperationalCompiler : UniformOperationalCompiler := by
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp searched_partrec)
  refine ⟨u, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id, ?_⟩
  intro code xs v
  rw [compile, Nat.Partrec.Code.eval_curry, hu]
  change v ∈ Nat.rfindOpt (obs (Nat.pair code (Encodable.encode xs))) ↔ _
  rw [obs_encode]
  exact searched_semantics code xs v

theorem totalBinaryCorrespondence : TotalBinaryCorrespondence := by
  obtain ⟨u, hu, hs⟩ := uniformOperationalCompiler
  refine ⟨u, hu, hs, ?_⟩
  intro code
  constructor
  · intro h xs
    obtain ⟨b, hb⟩ := h xs
    exact ⟨b, (hs code xs (bitValue b)).1 hb⟩
  · intro h xs
    obtain ⟨b, hb⟩ := h xs
    exact ⟨b, (hs code xs (bitValue b)).2 hb⟩

end LogicLineages.ComputabilityKnowledge.PredictionTapePartrecProof
