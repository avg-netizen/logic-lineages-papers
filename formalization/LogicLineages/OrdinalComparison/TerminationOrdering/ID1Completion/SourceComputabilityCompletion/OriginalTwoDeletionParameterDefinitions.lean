module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both deletion orders in the SAME original context and same outer context c.
All type lookups/deletion/erasure/parameter graphs are actual existing Programs. -/
def fields {alpha : Type}
    (gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight : OTerm alpha) : Formula alpha :=
  (OriginalContextInsertion.lengthGraph count gamma ⊓
    (OriginalContextInsertion.Below i (suc j) ⊓
      (OriginalContextInsertion.Below (suc j) count ⊓
        (graph2 InternalRawListRecursion.lookup a i gamma ⊓
          (graph2 InternalRawListRecursion.lookup b (suc j) gamma ⊓
            (graph2 OriginalClassContextAllPositionObserver.deleteAt upper (suc j) gamma ⊓
              (graph2 OriginalClassContextAllPositionObserver.deleteAt left i upper ⊓
                (graph2 OriginalClassContextAllPositionObserver.deleteAt lower i gamma ⊓
                  graph2 OriginalClassContextAllPositionObserver.deleteAt right j lower)))))))) ⊓
  (graph3 OriginalRawSyntaxTransport.erasePackedRaw rawUpper b (suc j) raw ⊓
    (graph3 OriginalRawSyntaxTransport.erasePackedRaw rawLeft a i rawUpper ⊓
      (graph3 OriginalRawSyntaxTransport.erasePackedRaw rawLower a i raw ⊓
        (graph3 OriginalRawSyntaxTransport.erasePackedRaw rawRight b j rawLower ⊓
          (graph2 InternalPairing.pairing paramLeft c left ⊓
            graph2 InternalPairing.pairing paramRight c right)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterDefinitions
