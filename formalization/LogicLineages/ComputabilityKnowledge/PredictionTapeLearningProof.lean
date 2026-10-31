module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeLearningTargets
public import LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecProof
public import LogicLineages.ComputabilityKnowledge.PredictionLearningProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeLearningProof
open PredictionTapeObservation PredictionTapeLearning PredictionTapeLearningTargets

private theorem pr_compile (u : Nat.Partrec.Code) : Primrec (PredictionVariableTapePartrec.compile u) :=
  Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id

theorem effectiveLearningMatrix : EffectiveLearningMatrix := by
  intro u
  have ha : Primrec (fun z : Nat × Nat × Nat × Nat =>
      (PredictionVariableTapePartrec.compile u z.1,
        PredictionVariableTapePartrec.compile u z.2.1, z.2.2.1, z.2.2.2)) :=
    ((pr_compile u).comp Primrec.fst).pair
      (((pr_compile u).comp (Primrec.fst.comp Primrec.snd)).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.comp
    (f := fun z : Nat.Partrec.Code × Nat.Partrec.Code × Nat × Nat =>
      PredictionLearning.learningMatrix z.1 z.2.1 z.2.2.1 z.2.2.2)
    (g := fun z : Nat × Nat × Nat × Nat =>
      (PredictionVariableTapePartrec.compile u z.1,
        PredictionVariableTapePartrec.compile u z.2.1, z.2.2.1, z.2.2.2))
    PredictionLearningProof.pr_matrix ha

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

theorem sourceLearningMatrix : SourceLearningMatrix := by
  obtain ⟨u, _, hsem, htotal⟩ := PredictionVariableTapePartrecProof.totalBinaryCorrespondence
  refine ⟨u, effectiveLearningMatrix u, ?_⟩
  intro p e hp he
  let hp' := (htotal p).2 hp
  let he' := (htotal e).2 he
  have h := PredictionLearningProof.learningFormula
    (PredictionVariableTapePartrec.compile u p) (PredictionVariableTapePartrec.compile u e) hp' he'
  rw [policy_eq u hsem p hp hp', policy_eq u hsem e he he'] at h
  exact h

end LogicLineages.ComputabilityKnowledge.PredictionTapeLearningProof
