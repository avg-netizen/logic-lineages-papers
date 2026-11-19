import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetBits
import LogicLineages.PersistentMarking.NumberedWindowArithmeticWitnessListCode

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCode
open Spine NumberedWindowArithmeticFields NumberedWindowArithmeticWitnessListCode
open NumberedWindowArithmeticDirectMultisetBits

/-- Literal natural fields: neither a target code nor a positive path
code is considered valid just by successful record decoding. -/
def encodeInsertion (e : InsertedOccurrence) : Nat :=
  encodeNode 4 [e.target,e.dominator,e.certificate]

def assembleInsertion : Nat → List Nat → Option InsertedOccurrence
  | 4, [target,dom,cert] => some ⟨target,dom,cert⟩
  | _, _ => none

def decodeInsertion (code : Nat) : Option InsertedOccurrence :=
  (decodeNode code).bind (fun p => assembleInsertion p.1 p.2)

def encodeDirectWitness (w : DirectMultisetWitness) : Nat :=
  encodeNode 5 [encodeFields w.kept,encodeFields w.removed,encodeListOf encodeInsertion w.inserted]

def assembleDirectWitness : Nat → List Nat → Option DirectMultisetWitness
  | 5, [k,r,a] => do
    let kept ← decodeFields k
    let removed ← decodeFields r
    let inserted ← decodeListOf decodeInsertion a
    pure ⟨kept,removed,inserted⟩
  | _, _ => none

def decodeDirectWitness (code : Nat) : Option DirectMultisetWitness :=
  (decodeNode code).bind (fun p => assembleDirectWitness p.1 p.2)

/-- Decode the literal ordered natural list, then check the actual
independent original typed scalar domain at every occurrence. -/
def typedAddressListCodeBit (S : Signature) (K : List Ty) (code : Nat) : Bool :=
  match decodeFields code with
  | none => false
  | some xs => typedAddressListBit S K xs

def directMultisetCodeBit (S : Signature) (K : List Ty) (src cert dst : Nat) : Bool :=
  match decodeFields src, decodeDirectWitness cert, decodeFields dst with
  | some source, some w, some target => directMultisetBit S K source target w
  | _, _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCode
