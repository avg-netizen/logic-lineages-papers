module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponentsDefinitions
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree
open RankedParse

/-- Genuine finite multiway cotrees: every internal node has at least two
children. Child order is present in data and forgotten by StructuralIso. -/
inductive Cotree where
  | atom
  | node (op : Operation) (n : Nat) (children : Fin (n + 2) → Cotree)

def Leaf : Cotree → Type
  | .atom => Unit
  | .node _ _ c => (i : _) × Leaf (c i)

def root : Cotree → Option Operation
  | .atom => none
  | .node o _ _ => some o

def Reduced : Cotree → Prop
  | .atom => True
  | .node o _ c => ∀ i, Reduced (c i) ∧ root (c i) ≠ some o

def chosenLeaf : (t : Cotree) → Leaf t
  | .atom => ()
  | .node _ _ c => ⟨0, chosenLeaf (c 0)⟩

def Adj : (t : Cotree) → Leaf t → Leaf t → Prop
  | .atom, _, _ => False
  | .node o _ c, ⟨i, x⟩, ⟨j, y⟩ =>
      if h : i = j then Adj (c j) (h ▸ x) y else o = .join

theorem adjSymm : ∀ (t : Cotree) (x y : Leaf t), Adj t x y → Adj t y x
  | .atom, _, _, h => False.elim h
  | .node o n c, ⟨i, x⟩, ⟨j, y⟩, h => by
      by_cases hij : i = j
      · subst j
        simp only [Adj, dif_pos rfl] at h ⊢
        exact adjSymm (c i) x y h
      · simpa only [Adj, dif_neg hij, dif_neg (Ne.symm hij)] using h

theorem adjIrrefl : ∀ (t : Cotree) (x : Leaf t), ¬ Adj t x x
  | .atom, _ => id
  | .node _ _ c, ⟨i, x⟩ => by
      simpa [Adj] using adjIrrefl (c i) x

def graph (t : Cotree) : SimpleGraph (Leaf t) where
  Adj := Adj t
  symm := ⟨adjSymm t⟩
  loopless := ⟨adjIrrefl t⟩

/-- Unordered rooted cotree isomorphism, preserving operations and all child
multiplicities through an actual index equivalence. -/
inductive StructuralIso : Cotree → Cotree → Prop where
  | atom : StructuralIso .atom .atom
  | node {o n m c d} (e : Fin (n + 2) ≃ Fin (m + 2)) :
      (∀ i, StructuralIso (c i) (d (e i))) →
      StructuralIso (.node o n c) (.node o m d)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree
