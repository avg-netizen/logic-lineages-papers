import LogicLineages.PersistentMarking.NativeTowerTypeCodeKernel
import LogicLineages.PersistentMarking.NativeTowerWitnessPrefixTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCode

namespace LogicLineages.PersistentMarking.NativeTowerTypeCodeTargets
open NativeTowerWitnessPrefixTargets (ty)
open NumberedWindowArithmeticTyCode (encodeTy)

def ExactNativeTowerTypeCode : Prop := ∀ n, typeCode n = encodeTy (ty n)

end LogicLineages.PersistentMarking.NativeTowerTypeCodeTargets
