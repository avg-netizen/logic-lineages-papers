module
public import Mathlib.Data.Finite.Sum
public import LogicLineages.ModelsAlgebra.Forests.RankedParseDefinitions
public import LogicLineages.ModelsAlgebra.Forests.FiniteIdealCoverDefinitions

/-! Actual finite simple graph images of ranked term ideals. Empty graphs are
included explicitly, and nonempty images are saturated under graph isomorphism.
This is the genuine ideal-cover context of repaired paper03 `lem:image-cover`,
not a postulate of effective ideal decomposition. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage
open RankedParse

instance leafFinite : (t : Term) → Finite (Leaf t)
  | .atom => inferInstanceAs (Finite Unit)
  | .node _ l r => by
    letI := leafFinite l
    letI := leafFinite r
    exact inferInstanceAs (Finite (Sum (Leaf l) (Leaf r)))

structure FiniteGraph where
  Vertex : Type
  finiteVertex : Finite Vertex
  edges : SimpleGraph Vertex

attribute [instance] FiniteGraph.finiteVertex

def evalFinite (t : Term) : FiniteGraph := ⟨Leaf t, inferInstance, graph t⟩

def Embeds (G H : FiniteGraph) : Prop := Nonempty (G.edges ↪g H.edges)

/-- Joint embedding for actual finite graphs (whose bundled carrier type lives
one universe above its vertices). -/
def GraphJEP (K : FiniteGraph → Prop) : Prop :=
  ∀ G H, K G → K H → ∃ W, K W ∧ Embeds G W ∧ Embeds H W

def GraphHereditary (K : FiniteGraph → Prop) : Prop :=
  ∀ G H, Embeds G H → K H → K G

structure IsIdeal (I : Term → Prop) : Prop where
  nonempty : ∃ t, I t
  downward : ∀ s t, Homeomorphic s t → I t → I s
  directed : ∀ s t, I s → I t → ∃ u, I u ∧ Homeomorphic s u ∧ Homeomorphic t u

def Image (I : Term → Prop) (G : FiniteGraph) : Prop :=
  IsEmpty G.Vertex ∨ ∃ t, I t ∧ Nonempty (G.edges ≃g graph t)

end LogicLineages.ModelsAlgebra.Forests.RankedGraphImage
