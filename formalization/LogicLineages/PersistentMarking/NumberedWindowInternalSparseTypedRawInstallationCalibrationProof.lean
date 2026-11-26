module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualAddressPositiveCalibration)
open NumberedWindowInternalSparsePathAdvanceNumericChecks (exact_AdvanceComposition)
open NumberedWindowInternalSparsePositiveFoldNumericChecks (exact_FoldComposition)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_AddressPositiveComposition)

/-- Keep the identical domain validators and least callback. All four
raw-dependent evaluations are derived afresh at the actual new raw. -/
theorem recheck (entries : Entries) (s : Settings) (cv tv : Program 1)
    (oldRaw newRaw : Program 5) (least : Program 3)
    (before : CallbacksAt entries s cv tv oldRaw least)
    (newCal : ActualRawCalibration entries s newRaw) :
    CallbacksAt entries s cv tv newRaw least ∧
      ActualAddressPositiveCalibration entries s cv tv newRaw least := by
  obtain ⟨ctxCal,typeCal,_,leastCal,_,_,_⟩ := before
  have advance := exact_AdvanceComposition entries s newRaw least newCal leastCal
  obtain ⟨fuel,positive⟩ := exact_FoldComposition entries s newRaw least advance
  exact ⟨⟨ctxCal,typeCal,newCal,leastCal,advance,fuel,positive⟩,
    exact_AddressPositiveComposition entries s cv tv newRaw least ctxCal typeCal positive⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationCalibrationProof
