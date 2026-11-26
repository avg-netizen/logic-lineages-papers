module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.RankedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Proof
open Continuation20261115 OriginalEncodedHeadConversion ClosureProof

theorem converted (n : Nat) : ValidOutput n (convert n) :=
  sum n _ _ (LeafProof.boolean n)
    (sum n _ _ (LeafProof.payload n 0)
      (sum n _ _ (LeafProof.payload n 1)
        (sum n _ _ (LeafProof.payload n 2) (RankedProof.ranked n))))

theorem internalConvertedValidity : Targets.InternalConvertedValidity := by
  intro n body alpha Delta encoded raw h
  exact converted n body alpha Delta ![encoded] raw h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Proof
