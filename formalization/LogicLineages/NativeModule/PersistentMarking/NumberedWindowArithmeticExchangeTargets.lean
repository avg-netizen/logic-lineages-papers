module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticExchangeAtomsTargets
public import LogicLineages.PersistentMarking.NumberedWindowExchangeAlgorithm

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeTargets
open NumberedWindowPrimaryExchangeBits NumberedWindowArithmeticExchangeAtomsTargets
open NumberedWindowArithmeticTermCode NumberedWindowSyntax NumberedWindowExchangeAlgorithm

def LiteralContextualExchange : Prop :=
  (∀ S K (q r : NTerm), (row (pairs S K) (encodeTerm q) (encodeTerm r)).1 = exchangeBit S K q r) ∧
  (∀ S K (as bs : NArgs), (row (pairs S K) (encodeArgs as) (encodeArgs bs)).2 = argsExchangeBit S K as bs)

def DecodedContextualExchange : Prop := ∀ S K a b, bits (pairs S K) a b =
  ((decodeTerm a).any (fun q => (decodeTerm b).any (exchangeBit S K q)),
   (decodeArgs a).any (fun qs => (decodeArgs b).any (argsExchangeBit S K qs)))

end LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeTargets
