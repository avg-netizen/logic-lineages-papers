module
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.CompletionTargets
open RankedParse

/-- Whole image-cover statement for the actual graph image of a term language.
Only the given finite term-ideal cover is assumed; graph coverage, heredity,
JEP and the final equality criterion must all be proved. The application
identifying the original forbidden graph class with this representation image,
and computing its ideal cover, remain distinct obligations. -/
def ImageCoverFromIdeals : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι]
    (I : ι → Term → Prop) (L : Term → Prop),
    (∀ i, IsIdeal (I i)) →
    (∀ t, L t ↔ ∃ i, I i t) →
    (∀ G, Image L G ↔ ∃ i, Image (I i) G) ∧
    (∀ i, GraphHereditary (Image (I i)) ∧ GraphJEP (Image (I i))) ∧
    (GraphJEP (Image L) ↔ ∃ i, ∀ G, Image L G ↔ Image (I i) G)

end LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.CompletionTargets
