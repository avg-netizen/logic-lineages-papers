module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Fold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- Auxiliary actual entry weight: Encodable entry is pair(type,raw), so take
its actual raw right projection and run the unchanged original bounds AST. -/
def entryWeight (n : Nat) : Program 1 :=
  .composition (Continuation20261115.OriginalCodeBoundsRecursion.bounds n)
    (fun _ : Fin 1 => InternalUnpair.right)
/-- General weighted sum/max fold, later specialized to entryWeight. This is
not an exchange replacement or a semantic permutation witness. -/
def step (weight : Program 1) : Program 2 :=
  .composition Continuation20261115.OriginalBoundsRecombination.merge
    ![.composition weight (fun _ : Fin 1 => .projection 0),.projection 1]
def weighted (weight : Program 1) : Program 1 :=
  InternalRawListRecursion.listRec (constant 0 0) (step weight)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Fold
