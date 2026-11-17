module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.TransportBaseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.Fold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- Auxiliary actual entry weight: Encodable entry is pair(type,raw), so take
its actual raw right projection and run the unchanged original bounds AST. -/
def step (weight : Program 1) : Program 2 :=
  .composition Continuation20261115.BoundsRecombination.merge
    ![.composition weight (fun _ : Fin 1 => .projection 0),.projection 1]
def weighted (weight : Program 1) : Program 1 :=
  InternalRawListRecursion.listRec (constant 0 0) (step weight)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.Fold
