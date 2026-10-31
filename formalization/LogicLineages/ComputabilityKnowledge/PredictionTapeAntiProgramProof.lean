module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerProof
public import LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecProof
public import LogicLineages.ComputabilityKnowledge.PredictionAntiProgramProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramProof
open PredictionTapeObservation PredictionTapeAntiProgram PredictionTapeAntiProgramTargets

private theorem policy_eq (u : Nat.Partrec.Code)
    (hsem : ∀ (code : Nat) (xs : List Bool) (v : Nat),
      v ∈ Nat.Partrec.Code.eval (PredictionVariableTapePartrec.compile u code) (Encodable.encode xs) ↔
        PredictionVariableTapePartrec.Produces code xs v)
    (code : Nat) (he : TotalBinary code)
    (hc : PredictionLearning.TotalBinary (PredictionVariableTapePartrec.compile u code)) :
    PredictionLearning.policy (PredictionVariableTapePartrec.compile u code) hc = policy code he := by
  funext xs
  have ho : PredictionLearning.bitValue
      (PredictionLearning.policy (PredictionVariableTapePartrec.compile u code) hc xs) ∈
      Nat.Partrec.Code.eval (PredictionVariableTapePartrec.compile u code) (Encodable.encode xs) :=
    Classical.choose_spec (hc xs)
  obtain ⟨b, hb, hv⟩ := (hsem code xs _).1 ho
  have hraw : policy code he xs ∈ PredictionUniformBinaryCompiler.binaryEval code xs :=
    Classical.choose_spec (he xs)
  have heq := Part.mem_unique hb hraw
  rw [heq] at hv
  cases h₁ : PredictionLearning.policy (PredictionVariableTapePartrec.compile u code) hc xs <;>
    cases h₂ : policy code he xs <;> simp_all [PredictionLearning.bitValue]

theorem uniformRawAntiProgram : UniformRawAntiProgram := by
  obtain ⟨reverse,hr,hsem,htotal⟩ := PredictionVariableTapePartrecProof.totalBinaryCorrespondence
  obtain ⟨forward,hf,hforward⟩ := PredictionTapePolicyCompilerProof.effectivePolicyTransport
  obtain ⟨anti,ha,_,hanti⟩ := PredictionAntiProgramProof.uniformCompiler
  have hc : Computable (compile forward reverse anti) :=
    Computable.comp (f := forward)
      (g := fun p => Encodable.encode (PredictionAntiProgram.compiledAnti anti
        (PredictionVariableTapePartrec.compile reverse p))) hf.to_comp
      (Computable.encode.comp (ha.comp hr.to_comp))
  refine ⟨forward,reverse,anti,hf,hc,?_⟩
  intro p hp
  let hp' := (htotal p).2 hp
  have hpol := policy_eq reverse hsem p hp hp'
  obtain ⟨he',hepol,_,_⟩ := hanti (PredictionVariableTapePartrec.compile reverse p) hp'
  obtain ⟨he,heq⟩ := hforward (PredictionAntiProgram.compiledAnti anti
    (PredictionVariableTapePartrec.compile reverse p)) he'
  have hfinal : policy (compile forward reverse anti p) he = PredictionGame.antiEvader (policy p hp) := by
    exact heq.trans (hepol.trans (congrArg PredictionGame.antiEvader hpol))
  refine ⟨he,hfinal,?_,?_⟩
  · rw [hfinal]
    exact PredictionGame.anti_disagrees _
  · rw [hfinal]
    exact PredictionGame.anti_not_learned _

end LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramProof
