import LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderCode

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddress
open NumberedWindowSyntax NumberedWindowArithmeticFields
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticBinderCode

/-- One address records the represented concrete binder stack, the
literal result type, and a candidate actual least original class code.
Signature and subtype window are fixed parameters of the whole theory. -/
structure ClassAddress where
  context : List Ty
  result : Ty
  least : Nat

def encodeAddress (a : ClassAddress) : Nat :=
  encodeNode 3 [encodeBinders a.context,encodeTy a.result,a.least]

def assembleAddress : Nat → List Nat → Option ClassAddress
  | 3, [ctx,ty,least] => do
    let Γ ← decodeBinders ctx
    let τ ← decodeTy ty
    pure ⟨Γ,τ,least⟩
  | _, _ => none

def decodeAddress (code : Nat) : Option ClassAddress :=
  (decodeNode code).bind (fun p => assembleAddress p.1 p.2)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddress
