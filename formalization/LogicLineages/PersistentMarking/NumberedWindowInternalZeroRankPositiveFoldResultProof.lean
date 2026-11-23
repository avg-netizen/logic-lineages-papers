module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldDecodeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldResultProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldCoreCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldResultProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualAdvanceCalibration)
open NumberedWindowInternalSparsePositiveFoldTargets (originalFold packedPositive)
open NumberedWindowInternalSparsePositiveFoldCoreCalibrationProof (composition)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankPositiveFoldInvariantProof (retainsZero)
open NumberedWindowInternalZeroRankPositiveFoldDecodeProof

private theorem oldAccepts (xs : Entries) (s : Settings) (raw : Program 5) (L : Program 3)
    (actual : ActualAdvanceCalibration xs s raw L) (c ty src cert dst : Nat) :
    (cert ≠ 0 ∧ originalFold xs s c ty (src+1) cert = some dst) ↔
      packedPositive xs s c ty src cert dst = true := by
  have old := (composition xs s raw L actual).2 c ty src cert dst
  rw [← exact_OriginalParameterizedPositive raw L,exact_ParameterizedPositiveValue,
    exact_ParameterizedOriginalFold xs s raw L actual] at old
  by_cases folded : cert ≠ 0 ∧ originalFold xs s c ty (src+1) cert = some dst <;>
    by_cases boolean : packedPositive xs s c ty src cert dst = true <;>
      simp [folded,boolean] at old ⊢

/-- Literal zero-positive evaluator: exactly original positive definedness
and target, together with the actual target's rank zero. This is a numeric
evaluation law, not an open object-calculus consequence. -/
theorem exact_OriginalZeroRankPositiveValue (xs : Entries) (s : Settings)
    (g : Program 1) (raw : Program 5) (L : Program 3)
    (actual : ActualAdvanceCalibration xs s raw L)
    (gFit : ∀ q, evaluate g (q ::ᵥ nil) = rawRank q)
    (c ty src cert dst : Nat) :
    evaluate (zeroPositive g raw L) (c ::ᵥ ty ::ᵥ src ::ᵥ cert ::ᵥ dst ::ᵥ nil) =
      if packedPositive xs s c ty src cert dst = true ∧ rawRank dst = 0 then 1 else 0 := by
  unfold zeroPositive
  rw [exact_ParameterizedPositiveValue]
  have accepts := oldAccepts xs s raw L actual c ty src cert dst
  by_cases nz : cert ≠ 0
  · rw [exact_OriginalZeroRankPhysicalFold xs s g raw L actual gFit c ty (src+1) cert nz]
    have exactGuard : (cert ≠ 0 ∧
        (originalFold xs s c ty (src+1) cert).filter retainsZero = some dst) ↔
        packedPositive xs s c ty src cert dst = true ∧ rawRank dst = 0 := by
      constructor
      · rintro ⟨hasCells,hit⟩
        obtain ⟨output,kept⟩ := Option.filter_eq_some_iff.mp hit
        exact ⟨accepts.mp ⟨hasCells,output⟩,by simpa only [retainsZero,beq_iff_eq] using kept⟩
      · rintro ⟨old,rankZero⟩
        obtain ⟨hasCells,output⟩ := accepts.mpr old
        exact ⟨hasCells,Option.filter_eq_some_iff.mpr
          ⟨output,by simp [retainsZero,rankZero]⟩⟩
    by_cases answer : packedPositive xs s c ty src cert dst = true ∧ rawRank dst = 0
    · rw [if_pos (exactGuard.mpr answer),if_pos answer]
    · rw [if_neg (fun h => answer (exactGuard.mp h)),if_neg answer]
  · have no : packedPositive xs s c ty src cert dst ≠ true :=
      fun isTrue => nz (accepts.mpr isTrue).1
    simp [nz,no]

theorem exact_OriginalZeroRankPositiveAccepts (xs : Entries) (s : Settings)
    (g : Program 1) (raw : Program 5) (L : Program 3)
    (actual : ActualAdvanceCalibration xs s raw L)
    (gFit : ∀ q, evaluate g (q ::ᵥ nil) = rawRank q)
    (c ty src cert dst : Nat) :
    evaluate (zeroPositive g raw L) (c ::ᵥ ty ::ᵥ src ::ᵥ cert ::ᵥ dst ::ᵥ nil) = 1 ↔
      packedPositive xs s c ty src cert dst = true ∧ rawRank dst = 0 := by
  rw [exact_OriginalZeroRankPositiveValue xs s g raw L actual gFit c ty src cert dst]
  by_cases holds : packedPositive xs s c ty src cert dst = true ∧ rawRank dst = 0 <;> simp [holds]

#print axioms exact_OriginalZeroRankPositiveValue
#print axioms exact_OriginalZeroRankPositiveAccepts

end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldResultProof
