module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAddressCheckersTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPositivePathChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressCheckersProof
open NumberedWindowAddressCheckers NumberedWindowArithmeticAddressCheckersTargets
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticScalarChecks
open NumberedWindowArithmeticDirectAlgorithmChecks NumberedWindowArithmeticAllContextBits

theorem domain : ExactMultisetDomain := by
  intro S K
  unfold multisetDomain
  rw [exact_ScalarAddress S K]
  exact exact_OriginalMultisetCheckerValues.1 S K

theorem certificates : ExactPositiveAndDirect := by
  intro S K step hs
  have callbacks : NumberedWindowPositivePathTargets.Callbacks S K step
      (NumberedWindowScalarAlgorithm.least (fixed S K)) := ⟨hs,exact_LeastRepresentative S K⟩
  have pos : positive (fixed S K) step = addressRSBit S K := by
    funext a c b
    exact NumberedWindowPositivePathChecks.exact_AddressRS S K step _ callbacks a c b
  refine ⟨pos,?_⟩
  unfold direct
  rw [exact_ScalarAddress S K,pos]
  exact exact_OriginalMultisetCheckerValues.2 S K
end LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressCheckersProof
