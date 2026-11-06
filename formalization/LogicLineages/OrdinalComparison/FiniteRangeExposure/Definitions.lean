module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure
open PolynomialGraphCompletion WordGuardCompletion

/-- Retained unsigned heads, evaluated in descending rank order. The target
outer rank is n+2; the original higher rank is n+m+3. -/
def exposurePrefix (n : Nat) : Nat → Nat → Word
  | 0, c => [kernelLetter (n+3) (c+(n+3)) 0]
  | m+1, c => kernelLetter (n+m+4) (c+(n+m+4)) 0 :: exposurePrefix n m c

def exposureWord (n m c : Nat) (j : Int) : Word :=
  exposurePrefix n m c++[SourceRangeExpansion.lowerHead n c j]

/-- Every retained unsigned kernel dominates its actual input. Thus the finite
maximum of exact source expansion tails pays every reached recursion step. -/
def exposureTail (n : Nat) : Nat → Nat → Int → Nat
  | 0, c, j => SourceRangeExpansion.expansionTail n c j
  | m+1, c, j => max (SourceRangeExpansion.expansionTail (n+m+1) c j) (exposureTail n m c j)

def contextTail (A S : Word) (n m c : Nat) (j : Int) : Nat :=
  max (reachTail A (exposureTail n m c j))
    (wordTail (A++[kernelLetter (n+m+3) c j]++S))

end LogicLineages.OrdinalComparison.FiniteRangeExposure
