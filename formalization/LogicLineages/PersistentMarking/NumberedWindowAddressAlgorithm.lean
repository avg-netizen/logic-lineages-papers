module

public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm
open NumberedWindowFieldAlgorithm

def nextType : Nat → List Bool → Bool
  | 0, _ => true
  | n+1, table =>
    match NumberedWindowPairAlgorithm.decode n with
    | none => false
    | some (a,b) => table.getD a false && table.getD b false

def typeTable : Nat → List Bool
  | 0 => []
  | n+1 => let table := typeTable n; table ++ [nextType n table]

def typeBit (n : Nat) := nextType n (typeTable n)

def contextView (n : Nat) : Option (List Nat) := do
  let stack ← unpack n
  if stack.all typeBit then pure stack else none

abbrev Address := List Nat × Nat × Nat

def addressView (n : Nat) : Option Address := do
  let (3, [ctx, result, least]) ← unpackNode n | none
  let stack ← contextView ctx
  if typeBit result then pure (stack,result,least) else none

end LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm
