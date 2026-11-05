module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceMeaningProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceProof
open SourceWitnessTrace

theorem unsupported (values : List Nat) (p : SourceFormula) (hp : FiniteSearchSource.test p = false) :
    solve values p.encode = none := by
  rw [solve, FiniteSearchProgramsProof.literalSyntaxCode p, hp]
  rfl

private theorem isSome_iff {A : Type} (o : Option A) : o.isSome = true ↔ ∃ a, o = some a := by
  cases o <;> simp

theorem exactSourceDomain : SourceWitnessTraceTargets.ExactSourceDomain := by
  intro values p
  refine ⟨?_, unsupported values p⟩
  by_cases hp : FiniteSearchSource.test p = true
  · rw [hp, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [isSome_iff, FiniteSearchSourceProof.actualTruth values p hp]
    simp_rw [actualLeastTrace values p hp]
    exact (least_exists _ p).symm
  · have hf := Bool.eq_false_iff.mpr hp
    rw [unsupported values p hf, hf]
    rfl

theorem exactTraceShape : SourceWitnessTraceTargets.ExactTraceShape := by
  intro values p ns hs
  have hp : FiniteSearchSource.test p = true := by
    by_cases hp : FiniteSearchSource.test p = true
    · exact hp
    · rw [unsupported values p (Bool.eq_false_iff.mpr hp)] at hs
      contradiction
  have hl := (actualLeastTrace values p hp ns).mp hs
  have hr := (leastRealizationSound _ _ _ hl).1
  exact ((originalEnvironment _ _ _).mp hr).1

theorem actualRawTrace : SourceWitnessTraceTargets.ActualRawTrace := by
  intro values code hp ns
  let p := SourceFormulaCodec.decode code
  have hc : p.encode = code := SourceFormulaCodecProof.codeRoundtrip code
  have ht : FiniteSearchSource.test p = true := by
    rw [← FiniteSearchProgramsProof.literalSyntaxCode p, hc]
    exact hp
  have h := actualLeastTrace values p ht ns
  simpa only [hc] using h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceProof
