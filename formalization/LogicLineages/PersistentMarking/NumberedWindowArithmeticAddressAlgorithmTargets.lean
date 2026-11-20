import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddress
import LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticBinderCode NumberedWindowAddressAlgorithm

def ExactTypeTable : Prop := ∀ n, typeTable n =
  (List.range n).map (fun i => (decodeTy i).isSome)

def ExactTypeGuard : Prop := ∀ n, typeBit n = (decodeTy n).isSome

def ExactBinderView : Prop := ∀ n, contextView n = (decodeBinders n).map (List.map encodeTy)

def address (a : ClassAddress) : Address := (a.context.map encodeTy, encodeTy a.result, a.least)

def ExactAddressView : Prop := ∀ n, addressView n = (decodeAddress n).map address

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmTargets
