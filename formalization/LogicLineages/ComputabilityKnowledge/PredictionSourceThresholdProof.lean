module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeLearningProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdProof
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionSourceThreshold PredictionSourceThresholdTargets

theorem effectiveThresholdMatrix : EffectiveThresholdMatrix := by
  intro u
  have hp : Primrec (fun z : Data => z.1) := Primrec.fst
  have hf : Primrec (fun z : Data => z.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun z : Data => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun z : Data => z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun z : Data => z.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : Primrec (fun z : Data => z.2.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hd : Primrec (fun z : Data => z.2.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hr : Primrec (fun z : Data => PredictionTapeMembershipMatrix.membershipMatrix z.2.2.1 z.2.1 z.2.2.2.1 z.2.2.2.2.1) :=
    Primrec.comp (f := fun z : Nat × Nat.Partrec.Code × Nat × Nat =>
      PredictionTapeMembershipMatrix.membershipMatrix z.1 z.2.1 z.2.2.1 z.2.2.2)
      (g := fun z : Data => (z.2.2.1, z.2.1, z.2.2.2.1, z.2.2.2.2.1))
      PredictionTapeMembershipMatrixProof.effectiveMembershipMatrix (he.pair (hf.pair (ha.pair hb)))
  have hs : Primrec (fun z : Data => PredictionTapeLearning.learningMatrix u z.1 z.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2) :=
    Primrec.comp (f := fun z : Nat × Nat × Nat × Nat =>
      PredictionTapeLearning.learningMatrix u z.1 z.2.1 z.2.2.1 z.2.2.2)
      (g := fun z : Data => (z.1, z.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2))
      (PredictionTapeLearningProof.effectiveLearningMatrix u) (hp.pair (he.pair (hc.pair hd)))
  exact Primrec.or.comp (Primrec.not.comp hr) hs

theorem sourceThreshold : SourceThreshold := by
  classical
  obtain ⟨u, _, hS⟩ := PredictionTapeLearningProof.sourceLearningMatrix
  refine ⟨u, effectiveThresholdMatrix u, ?_⟩
  intro p hp bound hf
  constructor
  · intro hT e a
    by_cases hR : ∀ b, PredictionTapeMembershipMatrix.membershipMatrix e bound a b = true
    · obtain ⟨he, htime⟩ := (PredictionTapeMembershipMatrixProof.sourceMembership e bound hf).2 ⟨a, hR⟩
      obtain ⟨c, hc⟩ := (hS p e hp he).1 (hT e he htime)
      exact ⟨0, c, fun d => by simp [thresholdMatrix, hR 0, hc d]⟩
    · obtain ⟨b, hb⟩ := not_forall.mp hR
      have hfalse : PredictionTapeMembershipMatrix.membershipMatrix e bound a b = false :=
        Bool.eq_false_iff.mpr hb
      exact ⟨b, 0, fun d => by simp [thresholdMatrix, hfalse]⟩
  · intro h e he htime
    obtain ⟨a, ha⟩ := (PredictionTapeMembershipMatrixProof.sourceMembership e bound hf).1 ⟨he, htime⟩
    obtain ⟨b, c, hc⟩ := h e a
    apply (hS p e hp he).2
    refine ⟨c, ?_⟩
    intro d
    have hd := hc d
    simpa only [thresholdMatrix, ha b, Bool.not_true, Bool.false_or] using hd

end LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdProof
