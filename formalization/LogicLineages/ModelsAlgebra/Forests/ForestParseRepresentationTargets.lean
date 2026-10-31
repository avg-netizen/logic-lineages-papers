module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.Targets
open GraphBridge RankedParse RankedGraphImage

/-- Actual source graph representation: nonempty finite order forests admit literal ranked parses. -/
def ForestRankedRepresentation : Prop :=
  ∀ (F : FiniteOrderForest), Nonempty F.Carrier →
    ∃ t : Term, Nonempty (comparabilityGraph F ≃g graph t)

/-- Exact identification of the original forbidden graph class with the parse image.
The source separately handles an empty forbidden graph; its remaining branch has
only nonempty forbidden forests. No representation correctness is a premise. -/
def ActualForbiddenLanguageImage : Prop :=
  ∀ (U : List FiniteOrderForest), (∀ B ∈ U, Nonempty B.Carrier) →
    ∀ G, ForbiddenClass U G ↔ Image (ForbiddenLanguage U) G

/-- The actual source image-cover lemma, including K=Forb(P4,C4,Comp(U)).
Its genuine finite term-ideal cover is the only decomposition hypothesis. -/
def ActualForbiddenIdealCover : Prop :=
  ∀ (U : List FiniteOrderForest), (∀ B ∈ U, Nonempty B.Carrier) →
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (I : ι → Term → Prop),
      (∀ i, IsIdeal (I i)) →
      (∀ t, ForbiddenLanguage U t ↔ ∃ i, I i t) →
      (∀ G, ForbiddenClass U G ↔ ∃ i, Image (I i) G) ∧
      (∀ i, GraphHereditary (Image (I i)) ∧ GraphJEP (Image (I i))) ∧
      (GraphJEP (ForbiddenClass U) ↔ ∃ i, ∀ G, ForbiddenClass U G ↔ Image (I i) G)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.Targets
