module
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyDefinitions

/-! The two explicit exceptional YES branches before source image-cover.
`none` leaves the general case unanswered; it is not a total JEP decider. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision
open ProfileAutomatonEncoding ProfileLanguageEmpty

def hasEmptyForbidden (F : List RawGraph) : Bool := F.any (fun A => decide (A.1 = 0))

def exceptionalDecision (F : List RawGraph) : Option Bool :=
  if hasEmptyForbidden F = true then some true
  else if sourceLanguageEmpty F = true then some true
  else none

end LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision
