module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetDefinitions
public import Mathlib.Logic.Equiv.Fin.Basic
@[expose] public section
/-! Explicit row-major serialization for fixed finite dimensions. Input is a
finite transition function, not a theorem asserting a machine semantics.
The varying-support enumeration needed by a global compiler is not assumed. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteSerialization
open Turing
abbrev FinAction (a : Nat) := Bool ⊕ Fin (a + 3)
abbrev FinMachine (q a : Nat) :=
  Fin (q + 1) → Fin (a + 3) → Option (Fin (q + 1) × FinAction a)

def numericAction {a : Nat} : FinAction a → PredictionFiniteAlphabet.Action
  | .inl b => .inl b
  | .inr s => .inr s.val

def numericEntry {q a : Nat} (x : Fin (q + 1) × FinAction a) : Nat × PredictionFiniteAlphabet.Action :=
  (x.1.val, numericAction x.2)

def rows {q a : Nat} (m : FinMachine q a) : List (Option (Nat × PredictionFiniteAlphabet.Action)) :=
  List.ofFn (fun i : Fin ((q + 1) * (a + 3)) => (m i.divNat i.modNat).map numericEntry)

def table {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a) : PredictionFiniteAlphabet.Table :=
  (a, start.val, rows m)

def code {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a) : Nat :=
  Encodable.encode (table start m)

def finiteStmt {a : Nat} : FinAction a → TM0.Stmt (Fin (a + 3))
  | .inl false => .move .left
  | .inl true => .move .right
  | .inr s => .write s

def finiteMachine {q a : Nat} (m : FinMachine q a) : TM0.Machine (Fin (a + 3)) (Fin (q + 1)) :=
  fun s b => (m s b).map (fun x => (x.1, finiteStmt x.2))

def embedCfg {q a : Nat} (c : TM0.Cfg (Fin (a + 3)) (Fin (q + 1))) : TM0.Cfg (Fin (a + 3)) Nat :=
  ⟨c.q.val, c.Tape⟩

end LogicLineages.ComputabilityKnowledge.PredictionFiniteSerialization
