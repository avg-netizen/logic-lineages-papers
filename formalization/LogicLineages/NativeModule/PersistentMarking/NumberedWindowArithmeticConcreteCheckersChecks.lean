module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticConcreteRulesProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticConcreteCheckersTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRootDispatchChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAddressCheckersChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteCheckersChecks
open NumberedWindowArithmeticConcreteCheckersTargets NumberedWindowArithmeticScalarTargets

theorem exact_WholeTypedStep : WholeTypedStep := by
  intro S K
  have root := NumberedWindowRootDispatchChecks.exact_RootDispatch S K _
    (NumberedWindowArithmeticConcreteRulesProof.calibrated S K)
  exact NumberedWindowRawContextChecks.exact_WindowStep S K _ _ root
    (fun Γ τ => (NumberedWindowArithmeticScalarChecks.exact_GuardedExchange S K Γ τ).1)

theorem exact_AllFourOriginalCheckers : AllFourOriginalCheckers := by
  intro S K
  exact ⟨NumberedWindowArithmeticScalarChecks.exact_ScalarAddress S K,
    NumberedWindowArithmeticAddressCheckersChecks.exact_MultisetDomain S K,
    NumberedWindowArithmeticAddressCheckersChecks.exact_PositiveAndDirect S K _ (exact_WholeTypedStep S K)⟩

#print axioms exact_WholeTypedStep
#print axioms exact_AllFourOriginalCheckers
end LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteCheckersChecks
