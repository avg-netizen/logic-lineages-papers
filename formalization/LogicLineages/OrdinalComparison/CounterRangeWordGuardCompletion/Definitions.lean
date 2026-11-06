module
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.RangePhiFactorization.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion

/-- Exactly the ordinary range letters of the source grammar. -/
def RangeHead (a : Letter) : Prop := a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3

/-- Phi has the literal identity preimage word; V and X lower only their
coherent signed index. No inverse counter or independent input is introduced. -/
def preimageWord (a : Letter) : Word :=
  if a.1 = 1 then [] else [RangePhiFactorization.predecessorHead a]

def rangeInputWord (B : Word) (a : Letter) : Word := B ++ preimageWord a

/-- Pay both the composed counter/Phi guard and the original range head at
its actual interior input. Phi's unused fields are harmlessly overpaid. -/
def guardTail (A B : Word) (n c : Nat) (a : Letter) (j k : Int) : Nat :=
  max (CounterPhiWordGuardCompletion.guardTail A (rangeInputWord B a) n c j k)
    (reachTail B (RangePhiFactorization.factorTail a))

end LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion
