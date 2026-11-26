import LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCode
import LogicLineages.PersistentMarking.Signature

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderCode
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticTyCode

/-- The actual finite nearest-binder-first list. In particular a binder
is not identified with a globally typed free name. -/
def encodeBinders : List Ty → Nat
  | [] => 0
  | σ :: Γ => pair (encodeTy σ) (encodeBinders Γ) + 1

def decodeBindersFuel : Nat → Nat → Option (List Ty)
  | _, 0 => some []
  | 0, _+1 => none
  | fuel+1, code+1 => do
    let (head,tail) ← decode code
    let σ ← decodeTy head
    let Γ ← decodeBindersFuel fuel tail
    pure (σ :: Γ)

def decodeBinders (code : Nat) : Option (List Ty) :=
  decodeBindersFuel code code

def codedLookup (code i : Nat) : Option Ty :=
  (decodeBinders code).bind (fun Γ => Γ[i]?)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderCode
