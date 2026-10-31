module
public import LogicLineages.OrdinalComparison.SourceBooleanWireDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanWire.Targets

def NodeExact : Prop := ∀ (n m : Nat) (a : Fin n → Nat) (w : Fin m → Bool)
    (g : Node n m) (b : Nat) (z : Fin 8 → Nat),
  LocalHolds a (fun i => bit (w i)) g b z ↔
    b = bit (evalNode a w g) ∧ z = canonicalAux a (fun i => bit (w i)) g

def WireExact : Prop := ∀ (n m : Nat) (d : Dag n m) (a : Fin n → Nat)
    (w : Fin m → Nat) (z : Fin m → Fin 8 → Nat),
  Holds d a w z ↔ w = (fun i => bit (evaluate d a i)) ∧ z = witnesses d a

def UniqueWitnesses : Prop := ∀ (n m : Nat) (d : Dag n m) (a : Fin n → Nat),
  ∃! p : (Fin m → Nat) × (Fin m → Fin 8 → Nat), Holds d a p.1 p.2

def RootCorrect : Prop := ∀ (n m : Nat) (d : Dag n m) (a : Fin n → Nat) (root : Fin m),
  (∃ w z, Holds d a w z ∧ w root = 1) ↔ evaluate d a root = true

/-- Concrete finite Boolean DAG overhead, NOT a substitute for the later
actual source-DAG lowering bound. Each new node contributes one bit and eight
auxiliary naturals, and at most nine Eq/Add/Sort arithmetic atoms. -/
def LinearOverhead : Prop :=
  (∀ (n m : Nat) (g : Node n m), (constraints g).length ≤ 9) ∧
  ∀ (n m : Nat) (d : Dag n m), atomCount d ≤ 9*m ∧ newWireCount d = 9*m
end LogicLineages.OrdinalComparison.Source.BooleanWire.Targets
