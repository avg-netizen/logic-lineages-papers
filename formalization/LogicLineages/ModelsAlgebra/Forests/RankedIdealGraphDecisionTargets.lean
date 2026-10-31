module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecisionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecision.Targets
open ProfileAutomatonEncoding ProfileSourceRegular RankedGraphImage ForestParseRepresentation
/-- Actual total source forbidden-graph JEP decision, including empty inputs,
empty forbidden graphs, and the empty nonempty-graph representation language. -/
 def GraphDecisionExact : Prop := ∀ F,
   graphDecision F = true ↔ GraphJEP (GeneralForbiddenClass (F.map rawFinite))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecision.Targets
