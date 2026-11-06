module
public import LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Exact source order: input, reverse retained mass, signed depth, outer shift. -/
def KernelShiftLexLT (c e : Nat) (j k a b : Int) (t u : Nat) : Prop :=
  t < u ∨ t = u ∧ (e < c ∨ c = e ∧ (j < k ∨ j = k ∧ a < b))

/-- The unshifted comparator is applied to the genuine coherent predecessors.
Both original-source factorization domains and the outer shift budget are paid. -/
def scalarTail (d c e : Nat) (j k a b : Int) : Nat :=
  max (equalityTail d c e (j-1) (k-1))
    (max (RangePhiFactorization.factorTail (kernelLetter d c j))
      (max (RangePhiFactorization.factorTail (kernelLetter d e k))
        (ShiftedPhiRangeWordGuardCompletion.scalarTail a b)))

def guardTail (A B : Word) (d c e : Nat) (j k a b : Int) : Nat :=
  max (reachTail A (scalarTail d c e j k a b))
    (reachTail B (scalarTail d c e j k a b))

def kernelNodesAt (d : Nat) (w : Word) : Nat :=
  (w.filter (fun a => (a.1 == 3) && (a.2.1 == d))).length

end LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion
