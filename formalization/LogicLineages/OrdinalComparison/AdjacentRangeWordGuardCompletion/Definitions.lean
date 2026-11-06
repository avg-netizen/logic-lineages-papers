module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.Definitions
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion

/-- The retained higher-rank occurrence stays attached to its original input. -/
def innerWord (A : Word) (n c : Nat) : Word :=
  A++[kernelLetter (n+3) (c+(n+3)) 0]

def kernelGuardTail (A B : Word) (n c e : Nat) (j k a b : Int) : Nat :=
  max (SourceRangeExpansion.contextTail A [shiftLetter a] (n+1) c j)
    (ShiftedEqualRankWordGuardCompletion.guardTail (innerWord A (n+1) c) B (n+3) c e j k a b)

def quadraticGuardTail (A B : Word) (c : Nat) (j k a b : Int) : Nat :=
  max (SourceRangeExpansion.contextTail A [shiftLetter a] 0 c j)
    (QuadraticWordGuardCompletion.guardTail (innerWord A 0 c) B
      (j-(((c+1)/2 : Nat) : Int)) k a b)

/-- Literal source range ranks; non-range letters receive zero only for counting. -/
def rangeRank (a : Letter) : Nat :=
  if a.1 = 1 then 1 else if a.1 = 2 then 2 else if a.1 = 3 then a.2.1 else 0

def rangeNodes (r : Nat) (w : Word) : Nat := (w.filter (fun a => rangeRank a == r)).length

end LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion
