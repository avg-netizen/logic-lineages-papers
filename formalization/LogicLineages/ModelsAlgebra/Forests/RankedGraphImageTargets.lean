module
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.Targets
open RankedParse

/-- Restriction transfer for an arbitrary actual nonempty simple graph,
not merely a graph already given by a ranked parse. -/
def PruneGraphEmbedding : Prop :=
  ∀ (V : Type) [Nonempty V] (G : SimpleGraph V) (t : Term),
    (G ↪g graph t) → ∃ s, Homeomorphic s t ∧ Nonempty (G ≃g graph s)

/-- Heredity and JEP of the actual isomorphism-saturated graph image of an ideal. -/
def IdealImage : Prop :=
  ∀ I, IsIdeal I →
    GraphHereditary (Image I) ∧
    GraphJEP (Image I)

/-- Covering graph types follows from covering the exact representation language,
including the separate empty-graph case. This is the cover construction, not
an assumption that the desired graph-image cover has already been proved. -/
def ImageCoverFromLanguage : Prop :=
  ∀ (ι : Type) [Nonempty ι] (I : ι → Term → Prop)
    (L : Term → Prop) (K : FiniteGraph → Prop),
    (∀ t, L t ↔ ∃ i, I i t) →
    (∀ G, K G ↔ IsEmpty G.Vertex ∨ ∃ t, L t ∧ Nonempty (G.edges ≃g graph t)) →
    ∀ G, K G ↔ ∃ i, Image (I i) G

/-- The finite-cover equivalence of paper03 `lem:image-cover`. The ideal cover
is its stated context, not an assumed implementation of the decision theorem.
The equality/cover hypothesis includes both containments on graph types. -/
def ImageCover : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι]
    (I : ι → Term → Prop) (K : FiniteGraph → Prop),
    (∀ i, IsIdeal (I i)) →
    (∀ G, K G ↔ ∃ i, Image (I i) G) →
    (∀ i, GraphHereditary (Image (I i)) ∧
      GraphJEP (Image (I i))) ∧
    (GraphJEP K ↔ ∃ i, ∀ G, K G ↔ Image (I i) G)

end LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.Targets
