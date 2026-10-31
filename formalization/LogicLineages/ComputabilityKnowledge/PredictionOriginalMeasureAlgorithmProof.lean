module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmTargets
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesProof
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmProof
open PredictionOriginalMeasureAlgorithm PredictionOriginalMeasureAlgorithmTargets
open PredictionOriginalMeasureMatrices OracleRelativeRecursion

private theorem indicator_binary (R : OraclePiThree.Matrix) (p : Nat) :
    OraclePiThree.matrixIndicator R p = 0 ∨ OraclePiThree.matrixIndicator R p = 1 := by
  classical
  simp only [OraclePiThree.matrixIndicator]
  split_ifs <;> simp

theorem relativeAlgorithm : RelativeAlgorithm := by
  intro u v hl hi
  let O : Set (Nat → Part Nat) := {fun n => Part.some (OraclePiThree.thirdJump n)}
  have hleft : ComputableIn O (fun z : Nat => z.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).computableIn
  have hip := OracleRelativeRecursionProof.relativeComposition O _ _ hi hleft
  have hp := OracleRelativeRecursionProof.relativeNumericPairing O _ _ hip hl
  have hc : Primrec (fun z : Nat => if z.unpair.1 = 1 then 0 else z.unpair.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
      (Primrec.const 0) (Primrec.snd.comp Primrec.unpair)
  have ht : ComputableIn O (searchTest u v) := by
    apply (OracleRelativeRecursionProof.relativeComposition O _ _ hc.computableIn hp).of_eq
    intro z
    simp only [searchTest, Nat.unpair_pair]
  have hs := OracleRelativeRecursionProof.relativePartialSearch O _ ht
  have ho : Primrec (fun z : Nat => if z.unpair.1 = 1 then 0 else z.unpair.2+1) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
      (Primrec.const 0) (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
  apply RecursiveIn.iff_nat.mpr
  apply ((RecursiveIn.iff_nat.mp ho.computableIn).comp
    ((RecursiveIn.iff_nat.mp hi).pair (RecursiveIn.iff_nat.mp hs))).of_eq
  intro p
  apply Part.ext
  intro x
  simp [result, Seq.seq, Part.mem_bind_iff, Part.mem_map_iff, eq_comm]

theorem exactOracleMeasure : ExactOracleMeasure := by
  classical
  intro g hg
  obtain ⟨u,v,hl,hi,hsem⟩ := PredictionOriginalMeasureMatricesProof.actualOriginalDecisions g hg
  refine ⟨u,v,relativeAlgorithm u v hl hi,?_⟩
  intro p hp
  obtain ⟨hlevel,hinf⟩ := hsem p hp
  by_cases ht : infinityDecision u v p = 1
  · have hz : 0 ∈ zeroSearch (searchTest u v) p := by
      simp [zeroSearch, Nat.mem_rfind, searchTest, ht]
    refine ⟨0,Part.eq_some_iff.mpr ?_,?_⟩
    · change 0 ∈ (zeroSearch (searchTest u v) p).map _
      rw [Part.mem_map_iff]
      exact ⟨0,hz,by simp [ht]⟩
    · simpa [outputValue] using (hinf.mp ht).symm
  · have hf : ∃ k, levelDecision u v (Nat.pair p k) = 0 := by
      by_contra hn
      have hall : ∀ k, levelDecision u v (Nat.pair p k) = 1 := by
        intro k
        exact (indicator_binary (levelMatrix u v) (Nat.pair p k)).resolve_left (fun h=>hn ⟨k,h⟩)
      apply ht
      apply hinf.mpr
      apply (PredictionTapeMeasureContractProof.infiniteCharacterization _ _).mpr
      intro m hm
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact (hlevel k).mp (hall k)
    let k := Nat.find hf
    have hk : levelDecision u v (Nat.pair p k) = 0 := Nat.find_spec hf
    have hmin : ∀ j < k, levelDecision u v (Nat.pair p j) = 1 := by
      intro j hj
      exact (indicator_binary (levelMatrix u v) (Nat.pair p j)).resolve_left (Nat.find_min hf hj)
    have hksearch : k ∈ zeroSearch (searchTest u v) p := by
      rw [zeroSearch, Nat.mem_rfind]
      constructor
      · simp [searchTest, ht, hk]
      · intro j hj
        simp [searchTest, ht, hmin j hj]
    refine ⟨k+1,Part.eq_some_iff.mpr ?_,?_⟩
    · change k+1 ∈ (zeroSearch (searchTest u v) p).map _
      rw [Part.mem_map_iff]
      exact ⟨k,hksearch,by simp [ht]⟩
    · have hnot : ¬ PredictionTapeRuntimeClass.Threshold (PredictionTapeObservation.policy p hp)
          (PredictionOriginalBounds.levelBound g (k+1)) := by
        intro h
        have := (hlevel k).mpr h
        omega
      have heq : PredictionOriginalHardness.originalHeight g (PredictionTapeObservation.policy p hp) =
          (k : WithTop Nat) := by
        by_cases hk0 : k=0
        · rw [hk0] at hnot ⊢
          exact (PredictionTapeMeasureContractProof.zeroCharacterization _ _).mpr hnot
        · apply (PredictionTapeMeasureContractProof.finiteCharacterization _
            (fun n => PredictionOriginalBounds.monotoneLevels g n) _ k (by omega)).mpr
          refine ⟨?_,hnot⟩
          have hprev := (hlevel (k-1)).mp (hmin (k-1) (by omega))
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hprev
      simpa [outputValue] using heq.symm

end LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmProof
