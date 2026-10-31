module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation
open GraphBridge RankedParse RankedGraphImage

/-- Arbitrary finite forbidden graph family, with P4 and C4 adjoined explicitly.
This covers the full family scope preceding source Lemma image-cover. -/
def GeneralForbiddenClass (B : List FiniteGraph) (G : FiniteGraph) : Prop :=
  ¬ Nonempty (fourPath ↪g G.edges) ∧ ¬ Nonempty (fourCycle ↪g G.edges) ∧
    ∀ H ∈ B, ¬ Embeds H G

def GeneralForbiddenLanguage (B : List FiniteGraph) (t : Term) : Prop :=
  GeneralForbiddenClass B (evalFinite t)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation
