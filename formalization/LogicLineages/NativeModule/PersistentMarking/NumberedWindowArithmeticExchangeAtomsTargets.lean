module

public import LogicLineages.PersistentMarking.NumberedWindowExchangeAtoms
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsTargets
open NumberedWindowPrimaryExchangeBits NumberedWindowHeadEnumerationTargets
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTermCode NumberedWindowSyntax
open NumberedWindowExchangeAtoms

def pairs (S : Spine.Signature) (K : List Ty) : HeadPairs :=
  (admittedHeads S K).flatMap (fun f => (equivalentHeads S K f).map (fun g => (encodeHead f,encodeHead g)))

def ExactHeadPairCheck : Prop := ∀ S K f g,
  allowed (pairs S K) (encodeHead f) (encodeHead g) = headPairBit S K f g

def ExactEncodedArguments : Prop := ∀ (qs : NArgs),
  NumberedWindowFieldAlgorithm.unpack (encodeArgs qs) = some (qs.toList.map encodeTerm)

def ExactLiteralPermutation : Prop := ∀ qs rs,
  bag (encodeArgs qs) (encodeArgs rs) = permutationBit qs rs

def ExactLiteralEquality : Prop :=
  (∀ q r, (encodeTerm q == encodeTerm r) = NumberedWindowLiteralEquality.termEq q r) ∧
  (∀ qs rs, (encodeArgs qs == encodeArgs rs) = NumberedWindowLiteralEquality.argsEq qs rs)
end LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsTargets
