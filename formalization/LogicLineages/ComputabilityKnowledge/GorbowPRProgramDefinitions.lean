module

public import Mathlib.Computability.Primrec.List

@[expose] public section

/-! Finite, arity-indexed primitive-recursive program syntax, with concrete
natural-number evaluation. This is a prerequisite for uniform defining
axioms in the existing Gorbow language, not a new Base or a representation
or Hilbert--Bernays assumption. No source statement of paper 12 is paid here.
The signature follows Mathlib's textbook `Nat.Primrec'`, avoiding primitive
pair/unpair operations in the eventual arithmetic defining equations. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open List.Vector

inductive Program : Nat → Type where
  | zero : Program 0
  | succ : Program 1
  | projection {n : Nat} (i : Fin n) : Program n
  | composition {m n : Nat} (f : Program n) (g : Fin n → Program m) : Program m
  | recursion {n : Nat} (f : Program n) (g : Program (n + 2)) : Program (n + 1)

def evaluate : {n : Nat} → Program n → List.Vector Nat n → Nat
  | _, .zero, _ => 0
  | _, .succ, v => Nat.succ v.head
  | _, .projection i, v => v.get i
  | _, .composition f g, v => evaluate f (List.Vector.ofFn fun i => evaluate (g i) v)
  | _, .recursion f g, v =>
      v.head.rec (evaluate f v.tail) fun y previous => evaluate g (y ::ᵥ previous ::ᵥ v.tail)

end LogicLineages.ComputabilityKnowledge.GorbowPRProgram
