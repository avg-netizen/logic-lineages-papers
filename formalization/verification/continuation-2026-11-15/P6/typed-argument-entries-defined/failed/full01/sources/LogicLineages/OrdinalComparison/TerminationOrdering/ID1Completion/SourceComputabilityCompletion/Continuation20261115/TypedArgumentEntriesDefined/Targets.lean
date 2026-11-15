module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRejectedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Acceptance by the unchanged original arguments checker forces the actual
standalone argumentEntries result to be Some entries, never failure zero.
All raw terms and checker H are arbitrary; no native typing, successful child
extract, constructor coverage or strong-induction hypothesis is assumed. -/
def InternalTypedDefined : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
    (Delta : List (Formula alpha)) (types raw gamma param value : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H types raw gamma)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) →
  Nonempty (Derivation body Delta (eqn value z).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.Targets
