module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def annotation := TransparentMetadataFields.annotation
def head (V : Program 3) (target : Bool) : Program 3 :=
  .composition OriginalHeadEncodingBridge.encodeHead (fun _ : Fin 1 => TransparentMetadataFields.head V target)
def label := TransparentMetadataFields.label
def types := TransparentMetadataFields.types
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields
