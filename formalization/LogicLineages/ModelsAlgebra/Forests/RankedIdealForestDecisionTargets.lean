module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecisionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecision.Targets
/-- Repaired paper 03 thm:decision on the original finite order-forest input,
using plain order embeddings and unrestricted finite permitted hosts. No
term-language JEP, graph-only replacement, or algorithm-correctness premise. -/
 def ForestDecisionExact : Prop := ∀ (U : List FiniteCode.Code) (hU : FiniteCode.FamilyValid U),
   forestDecision U = true ↔ CertificateSearch.HasJEP (FiniteCode.toFamily U hU)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecision.Targets
