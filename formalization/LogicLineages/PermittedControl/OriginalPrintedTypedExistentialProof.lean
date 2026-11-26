module
public import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialTargets
import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialSourceProof
import LogicLineages.PermittedControl.ActualBitFamilyTypedFuelProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedExistential
open ActualBitFamilyTypedFuel (exactTypedFamilySolve)

theorem exactOriginalPrintedTypedExistential : ExactOriginalPrintedTypedExistential := by
  intro f B selected known gates p topo plain positive
  have literal := exactOriginalLiteralFamilyExistential f known gates p plain positive
  have actual := exactOriginalTypedObservationExistential f known gates p topo plain positive
  have model := literal.trans actual
  have result := exactTypedFamilySolve f B selected (literalFamily known gates p positive)
  exact ⟨result.1.trans model,result.2.trans (not_congr model)⟩

end LogicLineages.PermittedControl.OriginalPrintedTypedExistential
