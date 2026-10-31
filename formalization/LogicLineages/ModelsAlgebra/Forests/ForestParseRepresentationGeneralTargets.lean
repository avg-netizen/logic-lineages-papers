module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationGeneralDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.GeneralTargets
open RankedParse RankedGraphImage

/-- Exact image identification for arbitrary additional forbidden finite graphs.
The empty-forbidden exceptional case is excluded exactly as in the source. -/
def GeneralForbiddenLanguageImage : Prop :=
  ∀ (B : List FiniteGraph), (∀ H ∈ B, Nonempty H.Vertex) →
    ∀ G, GeneralForbiddenClass B G ↔ Image (GeneralForbiddenLanguage B) G

/-- Full repaired image-cover lemma in its arbitrary finite graph-family scope.
P4/C4 are adjoined by definition; all other forbidden graphs are arbitrary.
No graph representation, graph-cover or effective ideal-decomposition oracle. -/
def GeneralForbiddenIdealCover : Prop :=
  ∀ (B : List FiniteGraph), (∀ H ∈ B, Nonempty H.Vertex) →
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (I : ι → Term → Prop),
      (∀ i, IsIdeal (I i)) →
      (∀ t, GeneralForbiddenLanguage B t ↔ ∃ i, I i t) →
      (∀ G, GeneralForbiddenClass B G ↔ ∃ i, Image (I i) G) ∧
      (∀ i, GraphHereditary (Image (I i)) ∧ GraphJEP (Image (I i))) ∧
      (GraphJEP (GeneralForbiddenClass B) ↔
        ∃ i, ∀ G, GeneralForbiddenClass B G ↔ Image (I i) G)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.GeneralTargets
