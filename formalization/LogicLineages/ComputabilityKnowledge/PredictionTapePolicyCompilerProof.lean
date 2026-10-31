module
public import LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerTargets
public import LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerProof
public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerProof
open PredictionTapePolicyCompiler PredictionTapePolicyCompilerTargets

private theorem decode_encode (c : Nat.Partrec.Code) : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c := by
  rw [← Nat.Partrec.Code.ofNatCode_eq]
  exact Denumerable.ofNat_encode c

private theorem bit_value (b : Bool) : b.toNat = PredictionLearning.bitValue b := by
  cases b <;> rfl

theorem effectivePolicyTransport : EffectivePolicyTransport := by
  obtain ⟨f, hf, hsem⟩ := PredictionUniformBinaryCompilerProof.universalBinaryCompiler
  refine ⟨f, hf, ?_⟩
  intro c hc
  have ht : PredictionTapeObservation.TotalBinary (transport f c) := by
    intro xs
    obtain ⟨b, hb⟩ := hc xs
    refine ⟨b, (hsem (Encodable.encode c) xs b).2 ?_⟩
    rwa [decode_encode, bit_value]
  refine ⟨ht, ?_⟩
  funext xs
  have hnew := Classical.choose_spec (ht xs)
  have hold : PredictionLearning.bitValue (PredictionLearning.policy c hc xs) ∈
      Nat.Partrec.Code.eval c (Encodable.encode xs) := Classical.choose_spec (hc xs)
  have hn := (hsem (Encodable.encode c) xs (PredictionTapeObservation.policy (transport f c) ht xs)).1 hnew
  rw [decode_encode, bit_value] at hn
  have he := Part.mem_unique hn hold
  cases h₁ : PredictionTapeObservation.policy (transport f c) ht xs <;>
    cases h₂ : PredictionLearning.policy c hc xs <;> simp_all [PredictionLearning.bitValue]

theorem uniformSelfHistoryTapeProgram : UniformSelfHistoryTapeProgram := by
  intro R hR
  obtain ⟨f, hf, htrans⟩ := effectivePolicyTransport
  obtain ⟨u, hu, _, hs⟩ := PredictionUniformHistoryProof.uniformSelfHistoryProgram R hR
  have hi : Computable (fun z => Encodable.encode (PredictionUniformHistory.compileSelfHistory u z)) :=
    Computable.comp (f := fun c : Nat.Partrec.Code => Encodable.encode c)
      (g := PredictionUniformHistory.compileSelfHistory u) Primrec.encode.to_comp hu
  have hg : Computable (compileSelfHistory f u) :=
    (Computable.comp (f := f)
      (g := fun z => Encodable.encode (PredictionUniformHistory.compileSelfHistory u z)) hf.to_comp hi).of_eq
      (fun _ => rfl)
  refine ⟨compileSelfHistory f u, hg, ?_⟩
  intro z
  obtain ⟨_, hc, hpolicy⟩ := hs z
  obtain ⟨ht, heq⟩ := htrans (PredictionUniformHistory.compileSelfHistory u z) hc
  exact ⟨ht, heq.trans hpolicy⟩

end LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerProof
