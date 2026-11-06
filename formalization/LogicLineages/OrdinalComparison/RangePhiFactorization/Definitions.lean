module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization
open PolynomialGraphCompletion WordGuardCompletion

/-- V or an admitted higher X, not a counter or an arbitrary range oracle. -/
def RangeHead (a : Letter) : Prop := a.1 = 2 ∨ a.1 = 3

/-- Preserve the actual tag, degree and retained mass; lower only the signed
coherent iteration index. Unused numeric fields are not normalized away. -/
def predecessorHead (a : Letter) : Letter :=
  (a.1,a.2.1,a.2.2.1,a.2.2.2-1)

def factorTail (a : Letter) : Nat := max (letterTail a) (letterTail (predecessorHead a))
def wordFactorTail (A : Word) (a : Letter) : Nat := reachTail A (factorTail a)

/-- The original complete context pays its own domains; equal middle values
then transfer the outer suffix domains literally, including signed shifts. -/
def contextTail (A : Word) (a : Letter) (S : Word) : Nat :=
  max (wordFactorTail A a) (wordTail (A ++ [a] ++ S))

def cancellationTail (A B : Word) (a : Letter) : Nat :=
  max (wordTail A) (wordFactorTail B a)

end LogicLineages.OrdinalComparison.RangePhiFactorization
