module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCodeDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrderDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecisionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecision
open ProfileAutomatonEncoding RankedIdealSourceCode ProfileExceptionalDecision
/-- Source exceptional branches followed by finitely many actual graph-image
inclusion decisions against the computed regular ideal cover. -/
def graphDecision (F : List RawGraph) : Bool :=
  if hasEmptyForbidden F = true then true
  else if (sourceCover F).isEmpty = true then true
  else (sourceCover F).any (fun B => RankedIdealCodeOrder.inclusion (sourceCode F) B)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecision
