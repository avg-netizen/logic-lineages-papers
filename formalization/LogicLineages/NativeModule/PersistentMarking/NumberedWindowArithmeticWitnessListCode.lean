module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticWitnessListCode
open NumberedWindowSyntax NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode
universe u

/-- This list codec preserves literal order and duplicate occurrences. -/
def encodeListOf {α : Type u} (enc : α → Nat) (xs : List α) : Nat :=
  encodeFields (xs.map enc)

def decodeElements {α : Type u} (dec : Nat → Option α) : List Nat → Option (List α)
  | [] => some []
  | n :: ns => do
    let x ← dec n
    let xs ← decodeElements dec ns
    pure (x :: xs)

def decodeListOf {α : Type u} (dec : Nat → Option α) (code : Nat) : Option (List α) :=
  (decodeFields code).bind (decodeElements dec)

def encodeTermList (xs : List NTerm) : Nat := encodeListOf encodeTerm xs
def decodeTermList (n : Nat) : Option (List NTerm) := decodeListOf decodeTerm n

end LogicLineages.PersistentMarking.NumberedWindowArithmeticWitnessListCode
