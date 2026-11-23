module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchSelectionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaPositiveCalibrationProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalBetaSub (betaChecker Fits run2)
open NumberedWindowInternalBetaRootDispatch (root')
open NumberedWindowInternalBetaCheckerFitProof (guardSpec argSpec bodySpec)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
  (ActualAddressPositiveCalibration ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration)
open NumberedWindowInternalSparsePathAdvanceNumericChecks (exact_AdvanceComposition)
open NumberedWindowInternalSparsePositiveFoldNumericChecks (exact_FoldComposition)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_AddressPositiveComposition)

/-- Replace only the root program, then calibrate the actual enclosing typed
raw validator, advance, complete fold, and address positive checker on every
input. The same selected unmodified least and all same actual guards are used;
this theorem is numerical, not an equality of the old and new proof bodies. -/
theorem selected (entries : Entries) (s : Settings)
    (cv tv syntaxProg : Program 1) (original other windowProg least : Program 3)
    (old : ActualRoot (NumberedWindowConcreteCheckers.root entries s) original)
    (fallback : ActualFallback other)
    (syntaxFit : ActualRawSyntax syntaxProg) (windowFit : ActualPackedWindow s windowProg)
    (ctxFit : ActualContextGuard cv) (tyFit : ActualTypeGuard tv)
    (leastFit : ActualLeastCalibration s least) :
    ∃ guard arg body sub : Program 2,
      Fits sub ∧
      (∀ src dst, run2 guard src dst = guardSpec src dst) ∧
      (∀ src dst, run2 arg src dst = argSpec src) ∧
      (∀ src dst, run2 body src dst = bodySpec src) ∧
      let root := root' original (betaChecker guard arg body sub)
      let raw := typedRaw5 root other windowProg syntaxProg
      ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
      CallbacksAt entries s cv tv raw least ∧
      ActualAddressPositiveCalibration entries s cv tv raw least := by
  obtain ⟨g,a,b,sub,hsub,hg,ha,hb,rootFit⟩ :=
    NumberedWindowInternalBetaRootDispatchSelectionProof.selected entries s original old
  let root := root' original (betaChecker g a b sub)
  let raw := typedRaw5 root other windowProg syntaxProg
  have rawFit := exact_TypedRaw5Calibration entries s root other windowProg syntaxProg
    rootFit fallback syntaxFit windowFit
  have advance := exact_AdvanceComposition entries s raw least rawFit leastFit
  obtain ⟨fuel,positive⟩ := exact_FoldComposition entries s raw least advance
  have value := exact_AddressPositiveComposition entries s cv tv raw least ctxFit tyFit positive
  exact ⟨g,a,b,sub,hsub,hg,ha,hb,rootFit,⟨ctxFit,tyFit,rawFit,leastFit,advance,fuel,positive⟩,value⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaPositiveCalibrationProof
