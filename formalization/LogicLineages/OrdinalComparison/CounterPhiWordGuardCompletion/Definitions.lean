module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion

/-- The original-source bridge, exact leader-word calibration, rational leader
bounds and the requested gap are all paid at the actual counter argument. -/
def counterTail (n c K : Nat) : Nat :=
  max (CounterLeaderBounds.threshold n c)
    (max (CounterWordGuardCompletion.leaderTail n c) (c+(n+3)+1+K))

def rangeTail (K : Nat) : Nat := K+1

def guardTail (A B : Word) (n c : Nat) (j k : Int) : Nat :=
  max (reachTail A (counterTail n c (j.natAbs+k.natAbs)))
    (reachTail B (rangeTail (j.natAbs+k.natAbs)))

end LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion
