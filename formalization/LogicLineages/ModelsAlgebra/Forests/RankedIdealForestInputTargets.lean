module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInputDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput.Targets
open ProfileAutomatonEncoding ProfileSourceRegular GraphBridge RankedGraphImage ForestParseRepresentation

def EncodedGraphExact : Prop := ∀ c (hc : FiniteCode.valid c = true),
  rawGraph (encodeOne c) = comparabilityGraph (FiniteCode.toForest c hc)

def AvoidanceExact : Prop := ∀ U (hU : FiniteCode.FamilyValid U) (G : FiniteSimpleGraph),
  GraphAvoidsForbidden (FiniteCode.toFamily U hU) G ↔
    GeneralForbiddenClass ((encode U).map rawFinite) (pack G)

/-- Exact original finite order-forest JEP, not merely graph-class JEP.
The input is a finite relation list with its existing validation predicate. -/
def ForestJEPExact : Prop := ∀ U (hU : FiniteCode.FamilyValid U),
  CertificateSearch.HasJEP (FiniteCode.toFamily U hU) ↔
    GraphJEP (GeneralForbiddenClass ((encode U).map rawFinite))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput.Targets
