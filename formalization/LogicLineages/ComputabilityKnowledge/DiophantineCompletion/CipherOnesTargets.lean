module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesTargets
open Cipher

/-- The actual sparse sums satisfy the arithmetic system, including the empty
vector case. This is a direction of the frozen original characterization. -/
def OnesEquationsForward : Prop := ∀ n q : Nat,
  n + 1 < q → OnesEquations n q (ones n q) (shiftedOnes n q)

/-- Uniqueness in the exact arithmetic system; no Diophantine premise and no
restricted input domain beyond the domain already present in the equations. -/
def OnesEquationsUnique : Prop := ∀ n q u u1 : Nat,
  OnesEquations n q u u1 → u = ones n q ∧ u1 = shiftedOnes n q

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesTargets
