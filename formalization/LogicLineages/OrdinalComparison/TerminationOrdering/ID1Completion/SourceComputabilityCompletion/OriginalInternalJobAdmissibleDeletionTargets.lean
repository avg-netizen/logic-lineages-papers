module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalInternalJobAdmissible
/-- Actual in-range context deletion/lookup and actual raw erasure suffice.
No context insertion or child acceptance is supplied. -/
def ActualDeletion : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (role typ raw gamma c count cutoff deleted erasedType erased : OTerm alpha),
 Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)) →
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw)) →
 Nonempty (Derivation body Delta (Admissible H M W role typ erased deleted c))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionTargets
