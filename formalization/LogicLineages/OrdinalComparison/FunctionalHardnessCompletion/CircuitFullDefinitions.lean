module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitGadgetDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitLinearTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull
open CircuitLinear Narendran LogicLineages.ComputabilityKnowledge.CircuitReduction

/-- The ordinary natural-number equation of one gate. The constant tag k still
means k+1. This is only an intermediate reading of the unchanged circuit. -/
def gateValue (v : Nat → Nat) : Gate → Nat
  | .constant k => k+1
  | .add x y => v x+v y
  | .mul x y => v x*v y

def GatesHold : Nat → List Gate → (Nat → Nat) → Prop
  | _, [], _ => True
  | next, gate::rest, v => v next=gateValue v gate ∧ GatesHold (next+1) rest v

/-- A single shared scalar assignment, positive on original circuit inputs.
Gate equations and the two original output references are kept literally. -/
def ScalarSolution (c : Circuit) (v : Nat → Nat) : Prop :=
  (∀ i, i<c.inputCount → 0<v i) ∧ GatesHold c.inputCount c.gates v ∧
    v c.leftOutput=v c.rightOutput

/-- Disjoint allocation tags for the exact builder. The three square witnesses
of a multiplication gate each receive four slots, even when inputs repeat.
Unused reserve slots exist but carry no extra scalar assumptions. -/
inductive Slot (n g : Nat) where
  | wire : Fin (n+g) → Slot n g
  | slack : Fin n → Slot n g
  | scalar : Fin g → Fin 4 → Slot n g
  | square : Fin g → Fin 3 → Fin 4 → Slot n g
  | constant : Fin 9 → Slot n g

def slotIndex {n g : Nat} : Slot n g → Nat
  | .wire i => i.val
  | .slack i => n+g+i.val
  | .scalar i j => (n+g)+n+4*i.val+j.val
  | .square i k j => polynomialAux n g+12*i.val+4*k.val+j.val
  | .constant j => constantAux n g+j.val

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull
