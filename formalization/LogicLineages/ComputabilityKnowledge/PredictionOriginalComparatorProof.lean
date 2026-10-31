module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorTargets
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmProof
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorProof
open PredictionOriginalComparator PredictionOriginalComparatorTargets

theorem exactOutputComparison : ExactOutputComparison := by
  constructor
  · exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 1)
        (Primrec.ite (Primrec.nat_lt.comp Primrec.fst Primrec.snd) (Primrec.const 1) (Primrec.const 0)))
  · intro a b
    constructor
    · simp only [compareOutputs]
      split_ifs <;> simp
    · by_cases ha : a=0
      · simp [compareOutputs, PredictionOriginalMeasureAlgorithm.outputValue, ha]
      · by_cases hb : b=0
        · simp [compareOutputs, PredictionOriginalMeasureAlgorithm.outputValue, ha,hb]
        · simp only [compareOutputs, if_neg ha, if_neg hb,
            PredictionOriginalMeasureAlgorithm.outputValue, WithTop.coe_lt_coe]
          split_ifs <;> simp_all <;> omega

private theorem recursive_comparison (u v : Nat.Partrec.Code)
    (h : RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)}
      (PredictionOriginalMeasureAlgorithm.result u v)) :
    RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} (comparison u v) := by
  have hl := (RecursiveIn.iff_nat.mp h).comp Nat.RecursiveIn.left
  have hr := (RecursiveIn.iff_nat.mp h).comp Nat.RecursiveIn.right
  have hc : Primrec (fun z : Nat => compareOutputs z.unpair.1 z.unpair.2) :=
    exactOutputComparison.1.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  apply RecursiveIn.iff_nat.mpr
  apply ((RecursiveIn.iff_nat.mp hc.computableIn).comp (hl.pair hr)).of_eq
  intro z
  apply Part.ext
  intro x
  simp [comparison, Seq.seq, Part.mem_bind_iff, Part.mem_map_iff, eq_comm]
  constructor
  · rintro ⟨a,b,⟨ha,hb⟩,hx⟩
    exact ⟨a,ha,b,hb,hx⟩
  · rintro ⟨a,ha,b,hb,hx⟩
    exact ⟨a,b,⟨ha,hb⟩,hx⟩

theorem actualComparatorUpper : ActualComparatorUpper := by
  intro g hg
  obtain ⟨u,v,hr,hs⟩ := PredictionOriginalMeasureAlgorithmProof.exactOracleMeasure g hg
  refine ⟨u,v,recursive_comparison u v hr,?_⟩
  intro p q hp hq
  obtain ⟨a,ha,hav⟩ := hs p hp
  obtain ⟨b,hb,hbv⟩ := hs q hq
  refine ⟨compareOutputs a b, ?_, (exactOutputComparison.2 a b).1, ?_⟩
  · simp [comparison,Nat.unpair_pair,ha,hb]
  · rw [← hav, ← hbv]
    exact (exactOutputComparison.2 a b).2

theorem fixedInfiniteComparatorReduction : FixedInfiniteComparatorReduction := by
  intro g hg
  obtain ⟨q,hq,hqinf⟩ := PredictionOriginalHardnessProof.infiniteOriginalPredictor g hg
  refine ⟨q,hq,hqinf,?_⟩
  intro R hR
  obtain ⟨m0,_,hred⟩ := PredictionOriginalHardnessProof.simultaneousOriginalReduction g hg
  obtain ⟨f,hf,hp,hs⟩ := hred R hR
  refine ⟨f,hf,hp,?_⟩
  intro z
  rw [hqinf, WithTop.lt_top_iff_ne_top]
  exact not_congr (hs z).2.1

end LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorProof
