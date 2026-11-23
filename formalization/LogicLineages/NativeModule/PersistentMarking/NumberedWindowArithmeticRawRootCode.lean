module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticWitnessListCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticBinderCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawWitnessRootBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticWitnessListCode
open NumberedWindowArithmeticBinderCode NumberedWindowPrimitiveWitnessBits
open NumberedWindowRawWitnessRootBits

def encodeFlag : Bool → Nat
  | false => 0
  | true => 1

def decodeFlag : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def encodeReplacement (w : ReplacementWitness) : Nat :=
  encodeNode 0 [encodeTermList w.kept,encodeTermList w.removed,encodeTermList w.added]

def assembleReplacement : Nat → List Nat → Option ReplacementWitness
  | 0, [p,q,r] => do
    let kept ← decodeTermList p
    let removed ← decodeTermList q
    let added ← decodeTermList r
    pure ⟨kept,removed,added⟩
  | _, _ => none

def decodeReplacement (code : Nat) : Option ReplacementWitness :=
  (decodeNode code).bind (fun p => assembleReplacement p.1 p.2)

def encodeRoot : RawRootWitness → Nat
  | .mark k => encodeNode 0 [k]
  | .lower => encodeNode 1 []
  | .select extra i domains => encodeNode 2 [encodeFlag extra,i,encodeBinders domains]
  | .copy => encodeNode 3 []
  | .stat w => encodeNode 4 [encodeReplacement w]
  | .fabs => encodeNode 5 []
  | .beta => encodeNode 6 []
  | .bottom => encodeNode 7 []

def assembleRoot : Nat → List Nat → Option RawRootWitness
  | 0, [k] => some (.mark k)
  | 1, [] => some .lower
  | 2, [ex,i,dom] => do
    let extra ← decodeFlag ex
    let domains ← decodeBinders dom
    pure (.select extra i domains)
  | 3, [] => some .copy
  | 4, [w] => (decodeReplacement w).map RawRootWitness.stat
  | 5, [] => some .fabs
  | 6, [] => some .beta
  | 7, [] => some .bottom
  | _, _ => none

def decodeRoot (code : Nat) : Option RawRootWitness :=
  (decodeNode code).bind (fun p => assembleRoot p.1 p.2)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCode
