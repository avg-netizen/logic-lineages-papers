module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticClassAddress
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathCheckBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextBits
open Spine NumberedWindowSyntax NumberedWindowTypingBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticPathCheckBits

/-- A successful literal raw term decode is not enough: it must actually
be admitted in the given finite context and be its own least class code. -/
def canonicalBit (S : Signature) (K : List Ty) (a : ClassAddress) : Bool :=
  match decodeTerm a.least with
  | none => false
  | some rep =>
    finiteWindowBit S K a.context a.result rep &&
      decide (leastCode S K a.context a.result rep = some a.least)

def addressBit (S : Signature) (K : List Ty) (code : Nat) : Bool :=
  match decodeAddress code with
  | none => false
  | some a => canonicalBit S K a

/-- One fixed signature/window admits all finite stacks and result types
as input data, but an actual raw class path never changes its own lexical
context or result type. Positive witness checking stays independent. -/
def addressRSBit (S : Signature) (K : List Ty) (src cert dst : Nat) : Bool :=
  match decodeAddress src, decodeAddress dst with
  | some a, some b =>
    decide (a.context = b.context) && decide (a.result = b.result) &&
      positiveClassPathCodeBit S K a.context a.result a.least cert b.least
  | _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextBits
