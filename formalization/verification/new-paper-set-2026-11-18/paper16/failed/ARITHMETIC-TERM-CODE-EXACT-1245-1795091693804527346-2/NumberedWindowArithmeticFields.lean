import LogicLineages.PersistentMarking.NumberedWindowArithmeticPair

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticFields
open NumberedWindowArithmeticPair (pair decode)

/-- Literal finite list fields, with zero for the empty list and a
positive pair per cons cell. No normalizing permutation of fields. -/
def encodeFields : List Nat → Nat
  | [] => 0
  | x::xs => pair x (encodeFields xs) + 1

def decodeFieldsFuel : Nat → Nat → Option (List Nat)
  | _, 0 => some []
  | 0, _+1 => none
  | fuel+1, code+1 => do
    let (x,tail) ← decode code
    let xs ← decodeFieldsFuel fuel tail
    pure (x::xs)

def decodeFields (code : Nat) : Option (List Nat) := decodeFieldsFuel code code

def encodeNode (tag : Nat) (fields : List Nat) : Nat :=
  pair tag (encodeFields fields) + 1

def decodeNode : Nat → Option (Nat × List Nat)
  | 0 => none
  | code+1 => do
    let (tag,body) ← decode code
    let fields ← decodeFields body
    pure (tag,fields)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticFields
