module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
public import LogicLineages.ComputabilityKnowledge.CircuitReduction

@[expose] public section

/-! Faithful prefix syntax for original ground-name O. Tags0–3 agree exactly
with the existing positive-expression prefix code; tags4,5,6 add zero,omega,
and the original ψ(ω·f+g) constructor. This is a syntax decoder, not a semantic
comparison algorithm for finite-valued collapse terms. -/
namespace LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCode

open WWOrdinalTermSemantics

def encode {d : Nat} : Term (Fin d) → List Nat
  | .one => [0]
  | .var i => [1, i.val]
  | .add a b => 2 :: (encode a ++ encode b)
  | .emul a b => 3 :: (encode a ++ encode b)
  | .zero => [4]
  | .omega => [5]
  | .collapse a b => 6 :: (encode a ++ encode b)

def height {d : Nat} : Term (Fin d) → Nat
  | .var _ | .zero | .one | .omega => 1
  | .add a b | .emul a b | .collapse a b => max (height a) (height b) + 1

def parse (d : Nat) : Nat → List Nat → Option (Term (Fin d) × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: xs => some (.one, xs)
  | _ + 1, 1 :: i :: xs => if h : i < d then some (.var ⟨i, h⟩, xs) else none
  | k + 1, 2 :: xs => do
      let (a, ys) ← parse d k xs
      let (b, zs) ← parse d k ys
      some (.add a b, zs)
  | k + 1, 3 :: xs => do
      let (a, ys) ← parse d k xs
      let (b, zs) ← parse d k ys
      some (.emul a b, zs)
  | _ + 1, 4 :: xs => some (.zero, xs)
  | _ + 1, 5 :: xs => some (.omega, xs)
  | k + 1, 6 :: xs => do
      let (a, ys) ← parse d k xs
      let (b, zs) ← parse d k ys
      some (.collapse a b, zs)
  | _, _ => none

def decode (d : Nat) (raw : List Nat) : Option (Term (Fin d)) := do
  let (t, rest) ← parse d (raw.length + 1) raw
  if rest = [] then some t else none

end LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCode
