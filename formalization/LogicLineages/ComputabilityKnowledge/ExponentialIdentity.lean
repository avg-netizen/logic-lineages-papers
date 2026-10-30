module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgram
public import LogicLineages.ComputabilityKnowledge.RaySeparation

@[expose] public section

/-! Literal uniform identity decision and positive separator for paper02 N4.
Both inputs use the existing prefix parser/normalizer. The original height
embeddings compare the resulting canonical maps at one common bound. A
nonidentity separator is the explicit accepted ray at its explicit threshold.
Malformed/out-of-arity inputs are rejected, not assigned a truth value. -/
namespace LogicLineages.ComputabilityKnowledge.ExponentialIdentity

open PositiveExpression RayFamilyClosure

def normalInputs (d : Nat) (a b : List Nat) : Option (HeightCode × HeightCode) := do
  let p ← ExponentialNormalizerProgram.normalizeCode d a
  let q ← ExponentialNormalizerProgram.normalizeCode d b
  pure (p, q)

def sameCode (d : Nat) (pq : HeightCode × HeightCode) : Bool :=
  decide (liftCode d (max pq.1.1 pq.2.1) pq.1 = liftCode d (max pq.1.1 pq.2.1) pq.2)

def decisionCode (d : Nat) (a b : List Nat) : Option Bool :=
  (normalInputs d a b).map (sameCode d)

def separatorCode (d : Nat) (a b : List Nat) : Option (List Nat) := do
  let pq ← normalInputs d a b
  if sameCode d pq then none else
    pure (RaySeparation.rayList d [pq.1, pq.2] (RaySeparation.threshold d [pq.1, pq.2]))

def positiveTuple (d : Nat) (xs : List Nat) (hpos : ∀ i : Fin d, 0 < xs.getD i.val 0) :
    Fin d → PosNat := fun i => ⟨xs.getD i.val 0, hpos i⟩

end LogicLineages.ComputabilityKnowledge.ExponentialIdentity
