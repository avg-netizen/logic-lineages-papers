module

public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! The ordered ranked alphabet a:0, U:2, J:2 from the repaired paper 03,
`decision.tex`, binary representations and Lemma `lem:parse-pruning`.
Leaf occurrences, rather than labels or quotient cotrees, are vertices.
No contraction or unordered child matching is built into the tree relation. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedParse

inductive Operation where
  | union | join
  deriving DecidableEq

inductive Term where
  | atom
  | node (op : Operation) (left right : Term)
  deriving DecidableEq

def Leaf : Term → Type
  | .atom => Unit
  | .node _ l r => Sum (Leaf l) (Leaf r)

def Adj : (t : Term) → Leaf t → Leaf t → Prop
  | .atom, _, _ => False
  | .node _ l _, .inl x, .inl y => Adj l x y
  | .node _ _ r, .inr x, .inr y => Adj r x y
  | .node o _ _, .inl _, .inr _ => o = .join
  | .node o _ _, .inr _, .inl _ => o = .join

theorem adj_symm : ∀ (t : Term) (x y : Leaf t), Adj t x y → Adj t y x
  | .atom, _, _, h => False.elim h
  | .node _ l _, .inl x, .inl y, h => adj_symm l x y h
  | .node _ _ r, .inr x, .inr y, h => adj_symm r x y h
  | .node _ _ _, .inl _, .inr _, h => h
  | .node _ _ _, .inr _, .inl _, h => h

theorem adj_irrefl : ∀ (t : Term) (x : Leaf t), ¬ Adj t x x
  | .atom, _ => id
  | .node _ l _, .inl x => adj_irrefl l x
  | .node _ _ r, .inr x => adj_irrefl r x

def graph (t : Term) : SimpleGraph (Leaf t) where
  Adj := Adj t
  symm := ⟨adj_symm t⟩
  loopless := ⟨adj_irrefl t⟩

/-- The dive/couple relation of GLS Example 7, on the exact ranked alphabet. -/
inductive Homeomorphic : Term → Term → Prop where
  | atom : Homeomorphic .atom .atom
  | left {s l r} (o) : Homeomorphic s l → Homeomorphic s (.node o l r)
  | right {s l r} (o) : Homeomorphic s r → Homeomorphic s (.node o l r)
  | couple {s₁ s₂ t₁ t₂} (o) : Homeomorphic s₁ t₁ → Homeomorphic s₂ t₂ →
      Homeomorphic (.node o s₁ s₂) (.node o t₁ t₂)

/-- An injective vertex map preserving and reflecting the actual evaluated adjacency. -/
structure InducedMap (s t : Term) where
  map : Leaf s → Leaf t
  injective : Function.Injective map
  adjacency : ∀ x y, Adj t (map x) (map y) ↔ Adj s x y

end LogicLineages.ModelsAlgebra.Forests.RankedParse
