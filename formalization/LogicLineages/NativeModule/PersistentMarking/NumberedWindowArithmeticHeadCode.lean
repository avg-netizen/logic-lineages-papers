module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTyCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticTyCode

/-- Every actual nominal head has its own constructor tag. The code
retains the full polymorphic declaration parameters and actual ranked
name and arity; equivalence classes are not collapsed. -/
def encodeHead : Head → Nat
  | .zero => pair 0 0
  | .succ => pair 1 0
  | .case τ => pair 2 (encodeTy τ)
  | .recursor τ => pair 3 (encodeTy τ)
  | .app σ τ => pair 4 (pair (encodeTy σ) (encodeTy τ))
  | .ranked name arity => pair 5 (pair name arity)

def decodeHeadParts : Nat → Nat → Option Head
  | 0, 0 => some .zero
  | 1, 0 => some .succ
  | 2, p => (decodeTy p).map Head.case
  | 3, p => (decodeTy p).map Head.recursor
  | 4, p => do
    let (dom,cod) ← decode p
    let σ ← decodeTy dom
    let τ ← decodeTy cod
    pure (.app σ τ)
  | 5, p => (decode p).map (fun q => Head.ranked q.1 q.2)
  | _, _ => none

def decodeHead (code : Nat) : Option Head := do
  let (tag,payload) ← decode code
  decodeHeadParts tag payload

end LogicLineages.PersistentMarking.NumberedWindowArithmeticHeadCode
