module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationTargets
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerProof
public import LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationProof
open PredictionOriginalClassification PredictionOriginalClassificationTargets PredictionOriginalHardness
open PredictionOriginalMeasureMatrices PredictionTapeObservation

private theorem indicator_iff (R : OraclePiThree.Matrix) (p : Nat) :
    OraclePiThree.matrixIndicator R p=1 ↔ ∀x,∃y,∀z,R (p,x,y,z)=true := by
  classical
  simp only [OraclePiThree.matrixIndicator]
  split_ifs <;> simp_all

theorem wholeSourceOriginalTheorem : WholeSourceOriginalTheorem := by
  intro g hg
  obtain ⟨u,v,_,_,hdec⟩ := PredictionOriginalMeasureMatricesProof.actualOriginalDecisions g hg.1
  have horder : ∀ p (hp : TotalBinary p) (m : Nat), 1 ≤ m →
      ((m : WithTop Nat) ≤ originalHeight g (policy p hp) ↔
        PredictionTapeRuntimeClass.Threshold (policy p hp) (PredictionOriginalBounds.levelBound g m)) := by
    intro p hp m hm
    exact PredictionMeasureOrderProof.positiveThresholdOrder _
      (PredictionOriginalBounds.monotoneLevels g) _ m hm
  have hlevel : ∀ m : Nat, 1 ≤ m →
      ∃ M : OraclePiThree.Matrix, Primrec M ∧ ∀ p (hp : TotalBinary p),
        ((m : WithTop Nat) ≤ originalHeight g (policy p hp) ↔ ∀x,∃y,∀z,M (p,x,y,z)=true) := by
    intro m hm
    let M : OraclePiThree.Matrix := fun z => levelMatrix u v (Nat.pair z.1 (m-1),z.2.1,z.2.2.1,z.2.2.2)
    refine ⟨M,?_,?_⟩
    · exact (PredictionOriginalMeasureMatricesProof.effectiveMatrices u v).1.comp
        ((Primrec₂.natPair.comp Primrec.fst (Primrec.const (m-1))).pair Primrec.snd)
    · intro p hp
      have hs := (hdec p hp).1 (m-1)
      rw [Nat.sub_add_cancel hm] at hs
      exact (horder p hp m hm).trans (hs.symm.trans (indicator_iff _ _))
  have hinf : ∃ M : OraclePiThree.Matrix, Primrec M ∧ ∀ p (hp : TotalBinary p),
      (originalHeight g (policy p hp)=⊤ ↔ ∀x,∃y,∀z,M (p,x,y,z)=true) :=
    ⟨infinityMatrix u v,(PredictionOriginalMeasureMatricesProof.effectiveMatrices u v).2,
      fun p hp => (hdec p hp).2.symm.trans (indicator_iff _ _)⟩
  obtain ⟨m0,hm0,hred⟩ := PredictionOriginalHardnessProof.simultaneousOriginalReduction g hg
  refine ⟨⟨m0,hm0,?_⟩,⟨hinf,?_⟩,?_,?_⟩
  · intro m hm
    refine ⟨hlevel m (le_trans hm0 hm),?_⟩
    intro R hR
    obtain ⟨f,hf,hp,hs⟩ := hred R hR
    exact ⟨f,hf,hp,fun z => (horder (f z) (hp z) m (le_trans hm0 hm)).trans ((hs z).2.2 m hm)⟩
  · intro R hR
    obtain ⟨f,hf,hp,hs⟩ := hred R hR
    exact ⟨f,hf,hp,fun z => (hs z).2.1⟩
  · obtain ⟨a,b,hr,hs⟩ := PredictionOriginalMeasureAlgorithmProof.exactOracleMeasure g hg.1
    exact ⟨⟨PredictionOriginalMeasureAlgorithm.result a b,hr,hs⟩,
      PredictionOriginalDegreeLowerProof.actualMeasureLower g hg⟩
  · obtain ⟨a,b,hr,hs⟩ := PredictionOriginalComparatorProof.actualComparatorUpper g hg.1
    exact ⟨⟨PredictionOriginalComparator.comparison a b,hr,hs⟩,
      PredictionOriginalDegreeLowerProof.actualComparatorLower g hg⟩

end LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationProof
