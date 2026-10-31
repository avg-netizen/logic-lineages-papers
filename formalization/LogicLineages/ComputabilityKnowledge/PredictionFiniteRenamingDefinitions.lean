module
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.Primrec.List
@[expose] public section
/-! Explicit list-index renaming, with default/blank at position zero.
Duplicates are allowed; first-index decoding remains exact on enumerated data.
This is a structural compiler adapter, not an assertion that an arbitrary
machine has a computably discoverable finite support. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteRenaming
open Turing

def items {α : Type} [Inhabited α] (tail : List α) : List α := default :: tail

def index {α : Type} [Inhabited α] [DecidableEq α] (tail : List α) (x : α) : Nat :=
  (items tail).idxOf x % (tail.length + 1)

def value {α : Type} [Inhabited α] (tail : List α) (n : Nat) : α :=
  (items tail).getI (n % (tail.length + 1))

def encode {α : Type} [Inhabited α] [DecidableEq α] (tail : List α) (x : α) : Fin (tail.length + 1) :=
  ⟨index tail x, Nat.mod_lt _ (by omega)⟩

def decode {α : Type} [Inhabited α] (tail : List α) (i : Fin (tail.length + 1)) : α :=
  (items tail).get ⟨i.val, by simpa [items] using i.isLt⟩

def toFinite {α : Type} [Inhabited α] [DecidableEq α] (tail : List α) :
    PointedMap α (Fin (tail.length + 1)) :=
  ⟨encode tail, by apply Fin.ext; simp [encode, index, items]⟩

def fromFinite {α : Type} [Inhabited α] (tail : List α) :
    PointedMap (Fin (tail.length + 1)) α :=
  ⟨decode tail, rfl⟩

def renamed {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ]
    (m : TM0.Machine Γ Λ) (states : List Λ) (alphabet : List Γ) :
    TM0.Machine (Fin (alphabet.length + 1)) (Fin (states.length + 1)) :=
  m.map (toFinite alphabet) (fromFinite alphabet) (toFinite states) (fromFinite states)

end LogicLineages.ComputabilityKnowledge.PredictionFiniteRenaming
