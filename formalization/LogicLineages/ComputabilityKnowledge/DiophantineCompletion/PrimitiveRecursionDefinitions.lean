module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Definitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursion

/-- Total extraction at the actual sparse cipher positions. -/
def digit (q code i : Nat) : Nat :=
  code / (Cipher.base q) ^ (2 ^ (i + 1)) % Cipher.base q

/-- Every trace entry is an actual output of the original partial evaluator.
There is no totality premise; an undefined base or step prevents a trace. -/
def partialTrace (base step : Nat.Partrec.Code) (a n : Nat) (f : Nat → Nat) : Prop :=
  f 0 ∈ Nat.Partrec.Code.eval base a ∧
    ∀ i, i < n → f (i + 1) ∈ Nat.Partrec.Code.eval step (Nat.pair a (Nat.pair i (f i)))

/-- A valid sparse cipher for all n+1 trace entries, including the base entry.
The original input parameter and final output are kept separately. -/
def codedTrace (base step : Nat.Partrec.Code) (a n y : Nat) : Prop :=
  ∃ q code : Nat, CipherRelation.Code (n + 1) q code ∧
    partialTrace base step a n (digit q code) ∧ digit q code n = y

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursion
