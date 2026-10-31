module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCodeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode.Targets
open RankedParse ProfileAutomatonEncoding ProfileSourceRegular RankedIdealRegularCode
open RankedGraphImage ForestParseRepresentation

def SourceCodeExact : Prop := ∀ F t,
  language (sourceCode F) t ↔ GeneralForbiddenLanguage (F.map rawFinite) t

def SourceCoverIdeals : Prop := ∀ F B, B ∈ sourceCover F → IsIdeal (language B)

/-- Exact source equation (1): an actual finite list of actual regular ideal
machines, with no representation, decomposition, ordering or numbering premise. -/
def SourceCoverExact : Prop := ∀ F t,
  GeneralForbiddenLanguage (F.map rawFinite) t ↔ ∃ B ∈ sourceCover F, language B t

def SourceCoverEmpty : Prop := ∀ F,
  sourceCover F = [] ↔ ∀ t, ¬GeneralForbiddenLanguage (F.map rawFinite) t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode.Targets
