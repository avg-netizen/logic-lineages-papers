module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- The comparison order of literal equal-rank kernels: input, reverse
retained mass, then signed index. No derived word value is made independent. -/
def KernelLexLT (c e : Nat) (j k : Int) (t u : Nat) : Prop :=
  t < u ∨ t = u ∧ (e < c ∨ c = e ∧ j < k)

/-- Both original raw inputs pay all interior domains and the exact common
kernel comparison region before the tail is entered. -/
def guardTail (A B : Word) (d c e : Nat) (j k : Int) : Nat :=
  max (reachTail A (equalityTail d c e j k))
    (reachTail B (equalityTail d c e j k))

end LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion
