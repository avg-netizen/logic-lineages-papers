module

public import LogicLineages.ComputabilityKnowledge.GorbowSyntax

@[expose] public section

/-! Literal full Gorbow term prefix syntax. Context validation is syntactic;
ambient arity is not an assertion that every context variable occurs. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCode
open GorbowSyntax

def encode {n : Nat} : Term n → List Nat
  | .var i => [0, i.val]
  | .zero => [1]
  | .succ t => 2 :: encode t
  | .add t u => 3 :: (encode t ++ encode u)
  | .mul t u => 4 :: (encode t ++ encode u)
  | .universalFunction t => 5 :: encode t

def height {n : Nat} : Term n → Nat
  | .var _ | .zero => 1
  | .succ t | .universalFunction t => height t + 1
  | .add t u | .mul t u => max (height t) (height u) + 1

def parse (n : Nat) : Nat → List Nat → Option (Term n × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: i :: xs => if h : i < n then some (.var ⟨i, h⟩, xs) else none
  | _ + 1, 1 :: xs => some (.zero, xs)
  | k + 1, 2 :: xs => do
      let (t, ys) ← parse n k xs
      some (.succ t, ys)
  | k + 1, 3 :: xs => do
      let (t, ys) ← parse n k xs
      let (u, zs) ← parse n k ys
      some (.add t u, zs)
  | k + 1, 4 :: xs => do
      let (t, ys) ← parse n k xs
      let (u, zs) ← parse n k ys
      some (.mul t u, zs)
  | k + 1, 5 :: xs => do
      let (t, ys) ← parse n k xs
      some (.universalFunction t, ys)
  | _, _ => none

def decode (n : Nat) (raw : List Nat) : Option (Term n) := do
  let (t, rest) ← parse n (raw.length + 1) raw
  if rest = [] then some t else none
end LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCode
