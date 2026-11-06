module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceRangeExpansion
open PolynomialGraphCompletion WordGuardCompletion

/-- At rank three the exposed child is the genuine quadratic V with its
ceiling-adjusted index, never a grammar-invalid rank-two X letter. -/
def lowerHead (n c : Nat) (j : Int) : Letter :=
  if n = 0 then quadraticLetter (j-(((c+1)/2 : Nat) : Int))
  else kernelLetter (n+2) c j

/-- Evaluation order: retain the higher-rank unsigned kernel first, then
expose the lower outer head. Retained mass is not subtracted from its output. -/
def expansionWord (n c : Nat) (j : Int) : Word :=
  [kernelLetter (n+3) (c+(n+3)) 0,lowerHead n c j]

/-- The genuine block threshold pays parent c+d+1 and inner c+2d+1 bridges;
actual original/replacement word domains are paid separately and explicitly. -/
def expansionTail (n c : Nat) (j : Int) : Nat :=
  max (finiteKernelRecursionThreshold (n+3) c j)
    (max (letterTail (kernelLetter (n+3) c j)) (wordTail (expansionWord n c j)))

def contextTail (A S : Word) (n c : Nat) (j : Int) : Nat :=
  max (reachTail A (expansionTail n c j))
    (wordTail (A++[kernelLetter (n+3) c j]++S))

end LogicLineages.OrdinalComparison.SourceRangeExpansion
