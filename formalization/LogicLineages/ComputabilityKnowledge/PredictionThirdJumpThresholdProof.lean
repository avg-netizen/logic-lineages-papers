module
public import LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdTargets
public import LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdProof
public import LogicLineages.ComputabilityKnowledge.OraclePiThreeProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdProof
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionThirdJumpThreshold PredictionThirdJumpThresholdTargets

theorem effectivePackedMatrix : EffectivePackedMatrix := by
  intro u
  have hp : Primrec (fun z : Nat × Nat × Nat × Nat => z.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hx : Primrec (fun z : Nat × Nat × Nat × Nat => z.2.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)
  have hy : Primrec (fun z : Nat × Nat × Nat × Nat => z.2.2.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec (fun z : Nat × Nat × Nat × Nat => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun z : Nat × Nat × Nat × Nat =>
      (z.1.unpair.1, Denumerable.ofNat Nat.Partrec.Code z.1.unpair.2,
       z.2.1.unpair.1, z.2.1.unpair.2, z.2.2.1.unpair.1, z.2.2.1.unpair.2, z.2.2.2)) :=
    (Primrec.fst.comp hp).pair (((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.snd.comp hp)).pair
      ((Primrec.fst.comp hx).pair ((Primrec.snd.comp hx).pair
        ((Primrec.fst.comp hy).pair ((Primrec.snd.comp hy).pair hd)))))
  exact Primrec.comp
    (f := fun z : PredictionSourceThreshold.Data => PredictionSourceThreshold.thresholdMatrix u
      z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2)
    (g := fun z : Nat × Nat × Nat × Nat =>
      (z.1.unpair.1, Denumerable.ofNat Nat.Partrec.Code z.1.unpair.2,
       z.2.1.unpair.1, z.2.1.unpair.2, z.2.2.1.unpair.1, z.2.2.1.unpair.2, z.2.2.2))
    (PredictionSourceThresholdProof.effectiveThresholdMatrix u) ha

theorem exactPackedFormula : ExactPackedFormula := by
  intro u p bound
  constructor
  · intro h e a
    obtain ⟨y, hy⟩ := h (Nat.pair e a)
    refine ⟨y.unpair.1, y.unpair.2, ?_⟩
    intro d
    simpa only [packedMatrix, Nat.unpair_pair, Denumerable.ofNat_encode] using hy d
  · intro h x
    obtain ⟨b, c, hc⟩ := h x.unpair.1 x.unpair.2
    refine ⟨Nat.pair b c, ?_⟩
    intro d
    simpa only [packedMatrix, Nat.unpair_pair, Denumerable.ofNat_encode] using hc d

theorem uniformThirdJumpThreshold : UniformThirdJumpThreshold := by
  classical
  obtain ⟨u, _, hu⟩ := PredictionSourceThresholdProof.sourceThreshold
  refine ⟨u, OraclePiThreeProof.actualPiThreeThirdJumpDecision (packedMatrix u) (effectivePackedMatrix u), ?_⟩
  intro p hp bound hf
  have hi : decision u (Nat.pair p (Encodable.encode bound)) = 1 ↔
      ∀ x, ∃ y, ∀ d, packedMatrix u (Nat.pair p (Encodable.encode bound), x, y, d) = true := by
    simp only [decision, OraclePiThree.matrixIndicator]
    split_ifs <;> simp_all
  exact hi.trans ((exactPackedFormula u p bound).trans (hu p hp bound hf).symm)

end LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdProof
