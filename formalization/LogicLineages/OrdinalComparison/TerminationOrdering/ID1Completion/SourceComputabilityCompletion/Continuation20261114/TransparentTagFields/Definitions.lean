module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def sourceCode : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)
def targetCode : Program 3 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 0)
def sourceRawTag : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => sourceCode)
def targetRawTag : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => targetCode)
/-- Invalid original node/window inputs retain the original zero field default. -/
def sourceTag (V : Program 3) : Program 3 :=
  InternalAcceptance.branch V (InternalAcceptance.constantZero 3) sourceRawTag
def targetTag (V : Program 3) : Program 3 :=
  InternalAcceptance.branch V (InternalAcceptance.constantZero 3) targetRawTag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields
