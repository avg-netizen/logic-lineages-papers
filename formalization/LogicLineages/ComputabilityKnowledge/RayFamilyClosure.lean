module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperations

@[expose] public section

/-! Explicit heterogeneous finite-family closure and common-height transport
for paper02 lem:ray. Heights are representation bounds for the source N1
finite trees. The accepted raiseForm embeds the same tree at the next bound;
iterating that original embedding, not numerical equivalence, defines the
common-height structural comparison. All code functions below are literal.
-/
namespace LogicLineages.ComputabilityKnowledge.RayFamilyClosure

open ExponentialNormalForm ExponentialHereditaryCodec ExponentialNormalFormProduct
open ExponentialNormalFormCodeOperations

abbrev HeightCode := Nat × Nat

noncomputable def raiseMany {d : Nat} : (extra h : Nat) → Form d h → Form d (h + extra)
  | 0, _, f => f
  | extra + 1, h, f => raiseForm (h + extra) (raiseMany extra h f)

def raiseManyCode (d h : Nat) : Nat → Nat → Nat
  | 0, n => canonicalize d h n
  | extra + 1, n => raiseCode d (h + extra) (raiseManyCode d h extra n)

def descendants : Nat → Nat → List HeightCode
  | 0, n => [(0, n)]
  | h + 1, n => (h + 1, n) :: (parseEntries n).flatMap (fun e => descendants h e.1)

def maxHeight (roots : List HeightCode) : Nat := roots.foldr (fun p acc => max p.1 acc) 0

def closedFamily (d : Nat) (roots : List HeightCode) : List HeightCode :=
  roots.flatMap (fun p => descendants p.1 p.2) ++
    (List.range (maxHeight roots + 1)).map (fun h => (h, zeroCode d h))

def liftCode (d H : Nat) (p : HeightCode) : Nat := raiseManyCode d p.1 (H - p.1) p.2

def liftedFamily (d : Nat) (roots : List HeightCode) : List Nat :=
  (closedFamily d roots).map (liftCode d (maxHeight roots))

noncomputable def SourceFamily (d : Nat) (roots : List HeightCode) : Prop :=
  ∀ p ∈ roots, CodeCanonical d p.1 p.2 ∧ WellFormed p.1 (formDecode d p.1 p.2)

noncomputable def CommonHeightEqual (d H : Nat) (p q : HeightCode) : Prop :=
  formDecode d H (liftCode d H p) = formDecode d H (liftCode d H q)

end LogicLineages.ComputabilityKnowledge.RayFamilyClosure
