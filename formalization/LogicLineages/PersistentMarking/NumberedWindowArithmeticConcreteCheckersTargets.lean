import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressCheckersTargets
import LogicLineages.PersistentMarking.NumberedWindowRawContextTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteCheckersTargets
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticAddressCheckersTargets (StepCalibration)
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticDirectCode

def WholeTypedStep : Prop := ∀ (S : Spine.Signature) K,
  StepCalibration S K (NumberedWindowConcreteCheckers.step S.entries (fixed S K))

def AllFourOriginalCheckers : Prop := ∀ (S : Spine.Signature) K,
  NumberedWindowScalarAlgorithm.scalar (fixed S K) = addressBit S K ∧
  NumberedWindowAddressCheckers.multisetDomain (fixed S K) = typedAddressListCodeBit S K ∧
  NumberedWindowConcreteCheckers.positive S.entries (fixed S K) = addressRSBit S K ∧
  NumberedWindowConcreteCheckers.direct S.entries (fixed S K) = directMultisetCodeBit S K

end LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteCheckersTargets
