module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextBits
public import Init.Data.List.Perm

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetBits
open Spine NumberedWindowArithmeticAllContextBits

/-- One inserted occurrence names an actual removed value and gives
its own genuine positive path certificate. Reuse of a removed value
by several inserted occurrences is permitted. -/
structure InsertedOccurrence where
  target : Nat
  dominator : Nat
  certificate : Nat

structure DirectMultisetWitness where
  kept : List Nat
  removed : List Nat
  inserted : List InsertedOccurrence

def typedAddressListBit (S : Signature) (K : List Ty) (xs : List Nat) : Bool :=
  xs.all (addressBit S K)

def insertionBit (S : Signature) (K : List Ty) (removed : List Nat)
    (e : InsertedOccurrence) : Bool :=
  decide (e.dominator ∈ removed) && addressRSBit S K e.dominator e.certificate e.target

/-- Check the actual supplied literal occurrence partition. Both
endpoint lists are typed, the removed list is nonempty, and a
zero-length inserted list is allowed. No partitions are searched. -/
def directMultisetBit (S : Signature) (K : List Ty) (source target : List Nat)
    (w : DirectMultisetWitness) : Bool :=
  typedAddressListBit S K source && typedAddressListBit S K target &&
    decide (source.Perm (w.kept ++ w.removed)) &&
    decide (target.Perm (w.kept ++ w.inserted.map InsertedOccurrence.target)) &&
    !w.removed.isEmpty && w.inserted.all (insertionBit S K w.removed)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetBits
