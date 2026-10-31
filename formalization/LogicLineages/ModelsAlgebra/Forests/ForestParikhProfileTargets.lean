module
public import LogicLineages.ModelsAlgebra.Forests.ForestParikhProfileDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhProfile.Targets
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open ForestParseRepresentationStates ForestParseRepresentationCounts

/-- Actual raw-family input through the executable profile machine, with no
externally supplied ordering or choice-based state numbering. -/
def ProfileFormulaExact : Prop := ∀ (F : List RawGraph) o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet (machine F) (.node o n c) ↔
    (profileFormula F o q).Realize (childCounts (machine F) c)

end LogicLineages.ModelsAlgebra.Forests.ForestParikhProfile.Targets
