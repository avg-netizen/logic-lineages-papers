module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsProof
public import LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdProof
public import LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesProof
public import LogicLineages.ComputabilityKnowledge.OracleJumpInclusionProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperProof
open PredictionCanonicalMeasureUpper PredictionCanonicalMeasureUpperTargets PredictionCanonicalTapeBounds
open PredictionTapeObservation OracleRelativeRecursion

theorem actualCanonicalThresholdOracle : ActualCanonicalThresholdOracle := by
  obtain ⟨u,hu,husem⟩ := PredictionThirdJumpThresholdProof.uniformThirdJumpThreshold
  obtain ⟨v,hv,hvsem⟩ := PredictionCanonicalTapeBoundsProof.actualSecondJumpBoundIndices
  let O : Set (Nat → Part Nat) := {fun n => Part.some (OraclePiThree.thirdJump n)}
  have hindex : ComputableIn O (positiveIndex v) := by
    apply hv.subst
    intro f hf
    have heq : f = fun n => Part.some (OracleJump.secondJump n) := hf
    subst f
    exact OracleJumpInclusionProof.actualSecondToThirdJumpInclusion
  have hright : ComputableIn O (fun z : Nat => z.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).computableIn
  have hleft : ComputableIn O (fun z : Nat => z.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).computableIn
  have hbound := OracleRelativeRecursionProof.relativeComposition O (positiveIndex v) _ hindex hright
  have hquery := OracleRelativeRecursionProof.relativeNumericPairing O _ _ hleft hbound
  have hselected : ComputableIn O (selectedDecision u v) :=
    OracleRelativeRecursionProof.relativeComposition O (PredictionThirdJumpThreshold.decision u) _ hu hquery
  refine ⟨u,v,hselected,?_⟩
  intro p hp k
  let bound := Denumerable.ofNat Nat.Partrec.Code (positiveIndex v k)
  have h := husem p hp bound (hvsem k).1
  have hencode : Encodable.encode bound = positiveIndex v k := Denumerable.encode_ofNat _
  rw [hencode] at h
  rw [show PredictionMaximum.evalValue bound = PredictionOriginalBounds.levelBound listing (k+1)
    from funext (hvsem k).2] at h
  simpa only [selectedDecision,Nat.unpair_pair] using h

private theorem decision_binary (u v : Nat.Partrec.Code) (z : Nat) :
    selectedDecision u v z=0 ∨ selectedDecision u v z=1 := by
  classical
  simp only [selectedDecision,PredictionThirdJumpThreshold.decision,OraclePiThree.matrixIndicator]
  split_ifs <;> simp

theorem canonicalFiniteUpper : CanonicalFiniteUpper := by
  classical
  obtain ⟨u,v,hcomp,hsem⟩ := actualCanonicalThresholdOracle
  have hsearch := OracleRelativeRecursionProof.relativePartialSearch _ _ hcomp
  have hresult : RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} (result u v) := by
    apply RecursiveIn.iff_nat.mpr
    apply (Nat.RecursiveIn.succ.comp (RecursiveIn.iff_nat.mp hsearch)).of_eq
    intro p
    apply Part.ext
    intro x
    simp [result, Part.mem_bind_iff, Part.mem_map_iff, eq_comm]
  refine ⟨u,v,hresult,?_⟩
  intro p hp
  obtain ⟨h,hfinite⟩ := PredictionSourceFiniteValuesProof.wholeSourceFiniteValues listing
    PredictionCanonicalTapeBoundsProof.exactCanonicalCoverage.1 p hp
  have hnotall : ¬ ∀ k, PredictionTapeRuntimeClass.Threshold (policy p hp)
      (PredictionOriginalBounds.levelBound listing (k+1)) := by
    intro hall
    have ht : PredictionOriginalHardness.originalHeight listing (policy p hp)=⊤ := by
      apply (PredictionTapeMeasureContractProof.infiniteCharacterization _ _).mpr
      intro m hm
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
      exact hall k
    rw [hfinite] at ht
    exact WithTop.coe_ne_top ht
  have hf : ∃ k, selectedDecision u v (Nat.pair p k)=0 := by
    push_neg at hnotall
    obtain ⟨k,hk⟩ := hnotall
    refine ⟨k,(decision_binary u v _).resolve_right ?_⟩
    intro hone
    exact hk ((hsem p hp k).mp hone)
  let k := Nat.find hf
  have hk : selectedDecision u v (Nat.pair p k)=0 := Nat.find_spec hf
  have hmin : ∀ j < k, selectedDecision u v (Nat.pair p j)=1 := by
    intro j hj
    exact (decision_binary u v _).resolve_left (Nat.find_min hf hj)
  have hksearch : k ∈ zeroSearch (selectedDecision u v) p := by
    rw [zeroSearch,Nat.mem_rfind]
    constructor
    · simp [hk]
    · intro j hj
      simp [hmin j hj]
  refine ⟨k,Part.eq_some_iff.mpr ?_,?_⟩
  · change k+1 ∈ (zeroSearch (selectedDecision u v) p).map Nat.succ
    rw [Part.mem_map_iff]
    exact ⟨k,hksearch,rfl⟩
  · have hnot : ¬ PredictionTapeRuntimeClass.Threshold (policy p hp)
        (PredictionOriginalBounds.levelBound listing (k+1)) := by
      intro ht
      have hh := (hsem p hp k).mpr ht
      omega
    by_cases hk0 : k=0
    · rw [hk0] at hnot ⊢
      exact (PredictionTapeMeasureContractProof.zeroCharacterization _ _).mpr hnot
    · apply (PredictionTapeMeasureContractProof.finiteCharacterization _
        (PredictionOriginalBounds.monotoneLevels listing) _ k (by omega)).mpr
      refine ⟨?_,hnot⟩
      have hprev := (hsem p hp (k-1)).mp (hmin (k-1) (by omega))
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hprev

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperProof
