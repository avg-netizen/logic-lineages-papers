module

public import LogicLineages.PersistentMarking.NumberedWindowAddressCheckers
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPositivePathTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressCheckersTargets
open NumberedWindowAddressCheckers NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticDirectCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticPathCheckBits
open NumberedWindowPositivePathAlgorithm (Step)

def ExactMultisetDomain : Prop := ∀ S K, multisetDomain (fixed S K) = typedAddressListCodeBit S K

def StepCalibration (S : Spine.Signature) (K : List Ty) (step : Step) : Prop := ∀ Γ τ q w r,
  step (Γ.map encodeTy) (encodeTy τ) q w r = windowStepCodeBit S K Γ τ q w r

def ExactPositiveAndDirect : Prop := ∀ S K step, StepCalibration S K step →
  positive (fixed S K) step = addressRSBit S K ∧ direct (fixed S K) step = directMultisetCodeBit S K
end LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressCheckersTargets
