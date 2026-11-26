module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalPresentationTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticConcreteCheckersChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectCodeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationChecks
open NumberedWindowOriginalPresentationTargets NumberedWindowPresentationClauses
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowArithmeticAllContextChecks NumberedWindowArithmeticDirectCodeChecks
open NumberedWindowExternalIDOperators

theorem exact_ActualOperatorAndTerms : ActualOperatorAndTerms := by
  intro S K hk P
  obtain ⟨hs, hj, hp, hd⟩ := NumberedWindowArithmeticConcreteCheckersChecks.exact_AllFourOriginalCheckers S K
  have sc := fun x => exact_AdmittedAddressBit S K x hk
  have mc := fun x => exact_TypedAddressListOnCodes S K x hk
  have pe := fun x y => exact_AddressPositivePath S K x y hk
  have de := fun x y => exact_DirectMultisetOnCodes S K x y hk
  constructor
  · intro z
    unfold tagged taggedStep scalarStep multisetStep guardedStep clause checks tagScalar tagMultiset
    simp only [hs, hj, hp, hd, sc, mc, pe, de]
  · unfold terms checks tagScalar
    simp only [hs, sc]

#print axioms exact_ActualOperatorAndTerms
end LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationChecks
