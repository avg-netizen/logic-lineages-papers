module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesTargets
public import LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdProof
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesProof
open PredictionOriginalMeasureMatrices PredictionOriginalMeasureMatricesTargets

theorem effectiveMatrices : EffectiveMatrices := by
  intro u v
  have hc : Primrec (PredictionOriginalBoundPrograms.compile v) :=
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const v) Primrec.id
  have hp : Primrec (fun z : Nat × Nat × Nat × Nat => z.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hl : Primrec (levelMatrix u v) :=
    (PredictionThirdJumpThresholdProof.effectivePackedMatrix u).comp
      ((Primrec₂.natPair.comp (Primrec.fst.comp hp)
        (Primrec.encode.comp (hc.comp (Primrec.succ.comp (Primrec.snd.comp hp))))).pair Primrec.snd)
  refine ⟨hl, ?_⟩
  have hx : Primrec (fun z : Nat × Nat × Nat × Nat => z.2.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)
  exact hl.comp ((Primrec₂.natPair.comp Primrec.fst (Primrec.fst.comp hx)).pair
    ((Primrec.snd.comp hx).pair (Primrec.snd.comp Primrec.snd)))

theorem exactInfinityPacking : ExactInfinityPacking := by
  intro u v p
  constructor
  · intro h k x
    simpa only [infinityMatrix, Nat.unpair_pair] using h (Nat.pair k x)
  · intro h x
    exact h x.unpair.1 x.unpair.2

theorem actualOriginalDecisions : ActualOriginalDecisions := by
  classical
  intro g hg
  obtain ⟨u, _, hu⟩ := PredictionSourceThresholdProof.sourceThreshold
  obtain ⟨v, _, hv⟩ := PredictionOriginalBoundProgramsProof.uniformOrdinaryBounds g hg
  refine ⟨u,v, OraclePiThreeProof.actualPiThreeThirdJumpDecision _ (effectiveMatrices u v).1,
    OraclePiThreeProof.actualPiThreeThirdJumpDecision _ (effectiveMatrices u v).2, ?_⟩
  intro p hp
  have hl : ∀ k, (∀ x, ∃ y, ∀ d, levelMatrix u v (Nat.pair p k,x,y,d) = true) ↔
      PredictionTapeRuntimeClass.Threshold (PredictionTapeObservation.policy p hp)
        (PredictionOriginalBounds.levelBound g (k+1)) := by
    intro k
    have ht := PredictionOriginalBoundProgramsProof.exactTotalBoundValues v g hv (k+1)
    simp only [levelMatrix, Nat.unpair_pair]
    rw [PredictionThirdJumpThresholdProof.exactPackedFormula]
    rw [← hu p hp _ ht.1]
    rw [show PredictionMaximum.evalValue (PredictionOriginalBoundPrograms.compile v (k+1)) =
      PredictionOriginalBounds.levelBound g (k+1) from funext ht.2]
  constructor
  · intro k
    have hi : levelDecision u v (Nat.pair p k) = 1 ↔
        ∀ x, ∃ y, ∀ d, levelMatrix u v (Nat.pair p k,x,y,d) = true := by
      simp only [levelDecision, OraclePiThree.matrixIndicator]
      split_ifs <;> simp_all
    exact hi.trans (hl k)
  · have hi : infinityDecision u v p = 1 ↔
        ∀ x, ∃ y, ∀ d, infinityMatrix u v (p,x,y,d) = true := by
      simp only [infinityDecision, OraclePiThree.matrixIndicator]
      split_ifs <;> simp_all
    rw [hi, exactInfinityPacking]
    change (∀ k, _) ↔ PredictionTapeMeasureContract.height _ _ = ⊤
    rw [PredictionTapeMeasureContractProof.infiniteCharacterization]
    constructor
    · intro h m hm
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact (hl k).mp (h k)
    · intro h k
      exact (hl k).mpr (h (k+1) (by omega))

end LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesProof
