module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def fields (U : Fin 19 → Program 3) (V : Program 3) (i : Fin 19) : Program 3 :=
  if i = 17 then HeadResultFields.result V false else
  if i = 18 then HeadResultFields.result V true else StructuralExchangeFields.fields U V i
def layer (U : Fin 19 → Program 3) (V : Program 3) : Program 3 :=
  TransparentExchangeLayer.optional (fields U V) V
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields
