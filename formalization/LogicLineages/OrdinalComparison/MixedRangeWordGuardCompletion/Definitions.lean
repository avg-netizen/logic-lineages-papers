module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.Definitions
public import LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion

def retainedWord (A : Word) (n m c : Nat) : Word := A++FiniteRangeExposure.exposurePrefix n m c

def kernelGuardTail (A B : Word) (n m c e : Nat) (j k a b : Int) : Nat :=
  max (FiniteRangeExposure.contextTail A [shiftLetter a] (n+1) m c j)
    (ShiftedEqualRankWordGuardCompletion.guardTail (retainedWord A (n+1) m c) B (n+3) c e j k a b)

def quadraticGuardTail (A B : Word) (m c : Nat) (j k a b : Int) : Nat :=
  max (FiniteRangeExposure.contextTail A [shiftLetter a] 0 m c j)
    (QuadraticWordGuardCompletion.guardTail (retainedWord A 0 m c) B
      (j-(((c+1)/2 : Nat) : Int)) k a b)

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion
