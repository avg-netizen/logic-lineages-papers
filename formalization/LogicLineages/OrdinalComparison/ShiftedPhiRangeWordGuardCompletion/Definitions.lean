module
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion CounterRangeWordGuardCompletion

/-- Once both outer Phi nodes are removed, offsets matter only at equal preimages. -/
def PreimageLexLT (j k : Int) (u v : Nat) : Prop := u < v ∨ u = v ∧ j < k

def scalarTail (j k : Int) : Nat := j.natAbs+k.natAbs+1

/-- Pay both generated preimage words and the original range head's exact
positive-depth factorization, all through their actual structural reach maps. -/
def guardTail (A B : Word) (a : Letter) (j k : Int) : Nat :=
  max (reachTail A (scalarTail j k))
    (max (reachTail (rangeInputWord B a) (scalarTail j k))
      (reachTail B (RangePhiFactorization.factorTail a)))

def phiNodes (w : Word) : Nat := (w.filter (fun a => a.1 == 1)).length

end LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion
