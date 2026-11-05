module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndex
open Cipher

/-- The actual sparse encoding of the sequence 0,1,...,n-1. -/
def index (n q : Nat) : Nat := encode n q id

/-- The shift-and-increment recurrence for the actual index sequence.
The source's auxiliary shifted code is eliminated; uniqueness is proved by
binary-adic contraction rather than assumed validity of an arbitrary input. -/
def IndexEquations (n q a : Nat) : Prop :=
  n+1<q ∧
    ((a*ones n q) &&& ((base q-1)*shiftedOnes n q)) + shiftedOnes n q =
      a+n*(base q)^(2^(n+1))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndex
