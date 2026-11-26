module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperBridgeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalPresentationChecks
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaChecks

/-! Proof of `BodyStageBridge` from the checked presentation (`exact_ConcretePresentation`:
programs with `Evaluates` and `Interprets`) and the checked operator calibration
(`exact_ActualOperatorAndTerms`: `tagged (checks …) P z ↔ taggedStep S K P z`). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperBridgeProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation PositiveArithmeticOperators
open NumberedWindowExternalIDOperators NumberedWindowGuardedNormTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalUpperBridgeTargets

theorem exact_BodyStageBridge : BodyStageBridge := by
  intro S K hk
  obtain ⟨i, j, r, d, evaluates, interprets⟩ :=
    NumberedWindowConcreteFormulaChecks.exact_ConcretePresentation S.entries (fixed S K)
  refine ⟨i, j, r, d, evaluates, fun c => ?_⟩
  have operatorEq : bodyOperator (sourceBody (NumberedWindowInternalPresentationTargets.data i j r d) c) =
      taggedStep S K := by
    funext P z
    apply propext
    exact ((interprets c P).1 z).trans
      ((NumberedWindowOriginalPresentationChecks.exact_ActualOperatorAndTerms S K hk P).1 z)
  refine ⟨operatorEq, fun a n => ?_⟩
  rw [operatorEq]

#print axioms exact_BodyStageBridge

end LogicLineages.PersistentMarking.ConditionalUpperBridgeProof
