module

public import LogicLineages.ComputabilityKnowledge.CircuitReduction

@[expose] public section

/-! Independent semantic comparator for paper02's circuit elimination stage.
No effectivity or MRDP conclusion is included in this semantic component.
Input values remain fixed while all wire and gadget values are existential.
Shared references name the same wire, not independent copies of subcircuits. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.CircuitReduction

open PositiveExpression
open LogicLineages.ComputabilityKnowledge.CircuitReduction

def Correctness : Prop :=
  ∀ (c : Circuit), c.WellFormed → ∀ ρ : Nat → PosNat,
    c.outputEqual ρ ↔ ∃ τ : Nat → PosNat,
      ExtendsInputs c.inputCount ρ τ ∧ ExponentialGap.AllEquations τ (compile c)

def DepthBound : Prop :=
  ∀ (c : Circuit), c.WellFormed → ∀ pair ∈ compile c,
    pair.1.depth ≤ 1 ∧ pair.2.depth ≤ 1

def VariablesBounded : Prop :=
  ∀ (c : Circuit), c.WellFormed → ∀ pair ∈ compile c,
    Bounded (variableBound c) pair.1 ∧ Bounded (variableBound c) pair.2

/-- Reserved auxiliaries are outside inputs/wires and pairwise distinct. -/
def FreshAuxiliaries : Prop :=
  ∀ (c : Circuit) (i j p q : Nat),
    i < c.gates.length → j < c.gates.length → p < 8 → q < 8 →
    let base := c.inputCount + c.gates.length
    base ≤ auxiliary base i p ∧ auxiliary base i p < variableBound c ∧
      (auxiliary base i p = auxiliary base j q ↔ i = j ∧ p = q)

def Target : Prop := Correctness ∧ DepthBound ∧ VariablesBounded ∧ FreshAuxiliaries

end LogicLineages.ComputabilityKnowledge.Comparators.CircuitReduction
