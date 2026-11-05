module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesUniquenessTargets
open Cipher

/-- A binary-adic contraction for the actual natural-number AND operation.
No finiteness bound or assumed digit representation is required. -/
def EvenMaskedSquareFixedPointUnique : Prop := ∀ A B w x y : Nat,
  2 ∣ x → 2 ∣ y →
  A + ((x*x) &&& w) = x + B →
  A + ((y*y) &&& w) = y + B → x = y

/-- The original explicit all-ones equations have at most one pair of natural
solutions. Existence and correspondence with the sparse sums remain separate. -/
def OnesEquationsAtMostOne : Prop := ∀ n q u u1 v v1 : Nat,
  OnesEquations n q u u1 → OnesEquations n q v v1 → u = v ∧ u1 = v1

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesUniquenessTargets
