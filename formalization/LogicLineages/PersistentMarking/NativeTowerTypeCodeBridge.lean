import LogicLineages.PersistentMarking.NativeTowerTypeCodeTargets

namespace LogicLineages.PersistentMarking.NativeTowerTypeCodeBridge
open NativeTowerTypeCodeTargets
open NativeTowerWitnessPrefixTargets (ty)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowArithmeticPair (pair)

/-- The rank-free alias is exactly the pair stored by the native codec. -/
theorem exactCodecPair (a b : Nat) : codecPair a b = pair a b := rfl

theorem exactNativeTowerTypeCode : ExactNativeTowerTypeCode := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change codecPair (typeCode n) (typeCode n) + 1 = pair (encodeTy (ty n)) (encodeTy (ty n)) + 1
    rw [ih,exactCodecPair]

#print axioms exactCodecPair
#print axioms exactNativeTowerTypeCode

end LogicLineages.PersistentMarking.NativeTowerTypeCodeBridge
