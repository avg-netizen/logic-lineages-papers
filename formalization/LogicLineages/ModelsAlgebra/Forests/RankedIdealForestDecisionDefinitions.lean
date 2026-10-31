module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecisionDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInputDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecision
/-- Total explicit algorithm on finite relation-list inputs. Its correctness is
asserted for exactly the existing validated finite order-forest input domain. -/
def forestDecision (U : List FiniteCode.Code) : Bool :=
  RankedIdealGraphDecision.graphDecision (RankedIdealForestInput.encode U)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecision
