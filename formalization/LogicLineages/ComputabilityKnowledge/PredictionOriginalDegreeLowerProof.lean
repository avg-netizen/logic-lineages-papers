module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerTargets
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorProof
public import LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerProof
open PredictionOriginalDegreeLower PredictionOriginalDegreeLowerTargets PredictionOriginalHardness

private theorem jump_binary (n : Nat) : OraclePiThree.thirdJump n = 0 ∨ OraclePiThree.thirdJump n = 1 := by
  classical
  simp only [OraclePiThree.thirdJump, OracleJump.jump]
  split_ifs <;> simp

private theorem output_top (n : Nat) : PredictionOriginalMeasureAlgorithm.outputValue n = ⊤ ↔ n=0 := by
  unfold PredictionOriginalMeasureAlgorithm.outputValue
  split_ifs <;> simp_all

theorem actualMeasureLower : ActualMeasureLower := by
  classical
  intro g hg A hA
  obtain ⟨R,hR,hjump⟩ := OracleThirdJumpNormalFormProof.recursiveActualThirdJumpComplement
  obtain ⟨m0,_,hred⟩ := PredictionOriginalHardnessProof.simultaneousOriginalReduction g hg
  obtain ⟨f,hf,hp,hs⟩ := hred R hR
  have hzero : ∀ z, A (f z)=0 ↔ OraclePiThree.thirdJump z=0 := by
    intro z
    rw [← output_top, hA (f z) (hp z)]
    exact (hs z).2.1.trans (hjump z)
  have ho : ComputableIn {fun n => Part.some (A n)} A := RecursiveIn.oracle _ rfl
  have hquery := OracleRelativeRecursionProof.relativeComposition _ _ _ ho hf.computableIn
  have hnorm : Primrec (fun n : Nat => if n=0 then 0 else 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  apply (OracleRelativeRecursionProof.relativeComposition _ _ _ hnorm.computableIn hquery).of_eq
  intro z
  change Part.some (if A (f z)=0 then 0 else 1) = Part.some (OraclePiThree.thirdJump z)
  congr 1
  rcases jump_binary z with hz|hz
  · simp [hz,(hzero z).2 hz]
  · have hn : A (f z) ≠ 0 := by intro h; have := (hzero z).1 h; omega
    simp [hz,hn]

theorem actualComparatorLower : ActualComparatorLower := by
  classical
  intro g hg A hA
  obtain ⟨R,hR,hjump⟩ := OracleThirdJumpNormalFormProof.recursiveActualThirdJumpComplement
  obtain ⟨q,hq,_,hred⟩ := PredictionOriginalComparatorProof.fixedInfiniteComparatorReduction g hg
  obtain ⟨f,hf,hp,hs⟩ := hred R hR
  have hquery : Computable (fun z => Nat.pair (f z) q) :=
    Primrec₂.natPair.to_comp.comp hf (Computable.const q)
  have ho : ComputableIn {fun n => Part.some (A n)} A := RecursiveIn.oracle _ rfl
  apply (OracleRelativeRecursionProof.relativeComposition _ _ _ ho hquery.computableIn).of_eq
  intro z
  congr 1
  have ha := hA (f z) q (hp z) hq
  have hone : A (Nat.pair (f z) q)=1 ↔ OraclePiThree.thirdJump z ≠ 0 :=
    ha.2.trans ((hs z).trans (not_congr (hjump z)))
  rcases jump_binary z with hz|hz
  · have hn : A (Nat.pair (f z) q) ≠ 1 := by intro h; exact (hone.mp h) hz
    rcases ha.1 with ha0|ha1
    · exact ha0.trans hz.symm
    · contradiction
  · have hn : OraclePiThree.thirdJump z ≠ 0 := by omega
    exact (hone.mpr hn).trans hz.symm

end LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerProof
