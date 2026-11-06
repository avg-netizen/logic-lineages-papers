module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.QuadraticSeparationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion

/-- Literal quadratic heads compare by their actual input, then coherent depth. -/
def CoreLexLT (j k : Int) (t u : Nat) : Prop := t < u ∨ t = u ∧ j < k

/-- Outer shifts decide only when both actual input and depth index agree. -/
def ShiftLexLT (j k a b : Int) (t u : Nat) : Prop :=
  t < u ∨ t = u ∧ (j < k ∨ j = k ∧ a < b)

/-- Pays the displayed degree-two separation region with one extra Phi step,
positive original depths, and the requested additive gap. -/
def scalarTail (j k : Int) (K : Nat) : Nat := j.natAbs+k.natAbs+K+8

def guardTail (A B : Word) (j k a b : Int) : Nat :=
  max (reachTail A (scalarTail j k (a.natAbs+b.natAbs)))
    (reachTail B (scalarTail j k (a.natAbs+b.natAbs)))

end LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion
