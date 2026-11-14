module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def fields (U : Fin 19 → Program 3) (V : Program 3) (i : Fin 19) : Program 3 :=
  if i = 0 then TransparentTagFields.sourceTag V else
  if i = 1 then EncodedMetadataFields.annotation V false else
  if i = 2 then EncodedMetadataFields.head V false else
  if i = 3 then EncodedMetadataFields.label V false else
  if i = 4 then EncodedMetadataFields.types V false else
  if i = 5 then TransparentChildFields.first V false else
  if i = 6 then TransparentChildFields.second V false else
  if i = 7 then TransparentTagFields.targetTag V else
  if i = 8 then EncodedMetadataFields.annotation V true else
  if i = 9 then EncodedMetadataFields.head V true else
  if i = 10 then EncodedMetadataFields.label V true else
  if i = 11 then EncodedMetadataFields.types V true else
  if i = 12 then TransparentChildFields.first V true else
  if i = 13 then TransparentChildFields.second V true else
  U i
def layer (U : Fin 19 → Program 3) (V : Program 3) : Program 3 :=
  TransparentExchangeLayer.optional (fields U V) V
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields
