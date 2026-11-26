import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetBits
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets
open Spine NumberedWindowArithmeticAllContextTargets
open NumberedWindowArithmeticDirectMultisetBits

def TypedAddressList (S : Signature) (K : List Ty) (xs : List Nat) : Prop :=
  ∀ a ∈ xs, AdmittedAddress S K a

/-- Independently specified original strict multiset replacement:
retain identical canonical occurrences, remove a nonempty multiset,
and insert only actual positive RS descendants of a removed value. -/
def StrictAddressReplacement (S : Signature) (K : List Ty) (source target : List Nat) : Prop :=
  ∃ kept removed added : List Nat,
    source.Perm (kept ++ removed) ∧ target.Perm (kept ++ added) ∧
      removed ≠ [] ∧ ∀ a ∈ added, ∃ b ∈ removed, AddressPositive S K b a

def AddressDirect (S : Signature) (K : List Ty) (source target : List Nat) : Prop :=
  TypedAddressList S K source ∧ TypedAddressList S K target ∧
    StrictAddressReplacement S K source target

def ExactTypedAddressListBit : Prop :=
  ∀ S K xs, DecisionSourceUniverse.Closed K →
    (typedAddressListBit S K xs = true ↔ TypedAddressList S K xs)

def SuppliedDirectMultisetSound : Prop :=
  ∀ S K source target w, DecisionSourceUniverse.Closed K →
    directMultisetBit S K source target w = true → AddressDirect S K source target

def ExactCertifiedDirectMultiset : Prop :=
  ∀ S K source target, DecisionSourceUniverse.Closed K →
    ((∃ w, directMultisetBit S K source target w = true) ↔ AddressDirect S K source target)

def StrictReplacementPreservesTypedAddresses : Prop :=
  ∀ S K source target, TypedAddressList S K source →
    StrictAddressReplacement S K source target → TypedAddressList S K target

def DirectMultisetRespectsPermutations : Prop :=
  ∀ S K source source' target target', source.Perm source' → target.Perm target' →
    (AddressDirect S K source target ↔ AddressDirect S K source' target')

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets
