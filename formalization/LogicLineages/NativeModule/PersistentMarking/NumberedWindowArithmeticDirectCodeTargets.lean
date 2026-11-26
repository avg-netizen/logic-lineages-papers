module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCodeTargets
open Spine NumberedWindowArithmeticFields
open NumberedWindowArithmeticDirectCode NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowArithmeticRawWitnessCodeTargets

def AdmittedAddressListCode (S : Signature) (K : List Ty) (code : Nat) : Prop :=
  ∃ xs : List Nat, encodeFields xs = code ∧ TypedAddressList S K xs

def DirectAtCode (S : Signature) (K : List Ty) (src dst : Nat) : Prop :=
  ∃ xs ys : List Nat, encodeFields xs = src ∧ encodeFields ys = dst ∧ AddressDirect S K xs ys

def ExactAddressListCodec : Prop := LiteralWitnessCodec encodeFields decodeFields

def ExactInsertedOccurrenceCodec : Prop := LiteralWitnessCodec encodeInsertion decodeInsertion

def ExactDirectMultisetWitnessCodec : Prop := LiteralWitnessCodec encodeDirectWitness decodeDirectWitness

def ExactTypedAddressListOnCodes : Prop :=
  ∀ S K code, DecisionSourceUniverse.Closed K →
    (typedAddressListCodeBit S K code = true ↔ AdmittedAddressListCode S K code)

def ExactDirectMultisetOnCodes : Prop :=
  ∀ S K src dst, DecisionSourceUniverse.Closed K →
    ((∃ cert, directMultisetCodeBit S K src cert dst = true) ↔ DirectAtCode S K src dst)

def OriginalCodedDirectDomains : Prop :=
  ∀ S K src dst, DirectAtCode S K src dst →
    AdmittedAddressListCode S K src ∧ AdmittedAddressListCode S K dst

def CodedDirectRejectsMalformed : Prop :=
  (∀ S K src, decodeFields src = none → typedAddressListCodeBit S K src = false) ∧
  (∀ S K src cert dst,
    (decodeFields src = none ∨ decodeDirectWitness cert = none ∨ decodeFields dst = none) →
      directMultisetCodeBit S K src cert dst = false)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCodeTargets
