module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAddressNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAddressChoiceProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankProgramProof (exact_OriginalRawNeutralRankProgram)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof (tape)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_ConcreteAddressPositive)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration ActualLeastCalibration ActualAdvanceCalibration)
open NumberedWindowInternalParameterizedAddressPositive (zeroAddress)
open NumberedWindowInternalZeroRankAddressNumericProof (exact_OriginalZeroRankAddressAccepts)

/-- Executable original settings-dependent physical rank-zero checker;
every underlying program is actually selected, with no caller oracle. -/
theorem exact_ChosenOriginalZeroRankAddress (entries : Entries) (s : Settings) :
    ∃ (cv tv g : Program 1) (raw : Program 5) (L : Program 3),
      ActualContextGuard cv ∧ ActualTypeGuard tv ∧
      ActualRawCalibration entries s raw ∧ ActualLeastCalibration s L ∧ ActualAdvanceCalibration entries s raw L ∧
      (∀ d, evaluate g (d ::ᵥ nil) = rawRank d) ∧
      ∀ x w y, evaluate (zeroAddress cv tv g raw L) (tape x w y) = 1 ↔
        NumberedWindowConcreteCheckers.positive entries s x w y = true ∧ rawRank (run rawLeast y) = 0 := by
  obtain ⟨cv,tv,raw,L,hcv,htv,hr,hL,ha,_,hp,had⟩ := exact_ConcreteAddressPositive entries s
  obtain ⟨g,hg⟩ := exact_OriginalRawNeutralRankProgram
  refine ⟨cv,tv,g,raw,L,hcv,htv,hr,hL,ha,hg,?_⟩
  intro x w y
  rw [exact_OriginalZeroRankAddressAccepts entries s cv tv g raw L ha hp hg x w y,had x w y]
  cases NumberedWindowConcreteCheckers.positive entries s x w y <;> simp

#print axioms exact_ChosenOriginalZeroRankAddress
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAddressChoiceProof
