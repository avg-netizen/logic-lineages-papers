module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPair

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairTargets
open NumberedWindowArithmeticPair

def PairComponentBounds : Prop := ∀ a b, a ≤ pair a b ∧ b ≤ pair a b

def ExactPairInjection : Prop := ∀ a b c d, pair a b = pair c d ↔ a = c ∧ b = d

def ExactPairDecode : Prop := ∀ n a b, decode n = some (a,b) ↔ pair a b = n

def PairRoundtrip : Prop := ∀ a b, decode (pair a b) = some (a,b)

def ExactNonPair : Prop := ∀ n, decode n = none ↔ ¬ ∃ a b, pair a b = n

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairTargets
