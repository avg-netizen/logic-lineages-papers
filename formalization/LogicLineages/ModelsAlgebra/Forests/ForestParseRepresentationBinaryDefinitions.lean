module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationFlatten

/-- A genuine ordered full binary skeleton, with a child-occurrence index at each leaf. -/
inductive Shape (I : Type) where
  | leaf : I → Shape I
  | node : Shape I → Shape I → Shape I

def Positions {I : Type} : Shape I → Type
  | .leaf _ => Unit
  | .node p q => Sum (Positions p) (Positions q)

def label {I : Type} : (q : Shape I) → Positions q → I
  | .leaf i, _ => i
  | .node p _, .inl x => label p x
  | .node _ q, .inr y => label q y

def rename {I J : Type} (f : I → J) : Shape I → Shape J
  | .leaf i => .leaf (f i)
  | .node p q => .node (rename f p) (rename f q)

/-- Replace every leaf of a same-operation skeleton by its indexed child parse. -/
def graft {I : Type} (o : Operation) (r : I → Term) : Shape I → Term
  | .leaf i => r i
  | .node p q => .node o (graft o r p) (graft o r q)

/-- Literal association/permutation expansion: every child occurrence appears once,
with an arbitrary full binary bracketing and ordering at each operation root. -/
inductive Expansion : Term → Cotree → Prop
  | atom : Expansion .atom .atom
  | node {o n c} (r : Fin (n + 2) → Term) (q : Shape (Fin (n + 2)))
      (children : ∀ i, Expansion (r i) (c i))
      (occurrences : Function.Bijective (label q)) :
      Expansion (graft o r q) (.node o n c)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary
