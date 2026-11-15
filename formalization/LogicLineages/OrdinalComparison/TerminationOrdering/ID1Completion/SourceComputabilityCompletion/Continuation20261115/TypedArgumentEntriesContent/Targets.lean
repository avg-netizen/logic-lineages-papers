module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Literal lengths of the actual extracted entry list and original accepted
argument-type list coincide. All terms and H are arbitrary; no native decoding
or length-alignment premise is present. -/
def InternalLength : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (types raw gamma param entries entryLength typeLength : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H types raw gamma)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph entryLength entries)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph typeLength types)) →
  Nonempty (Derivation body Delta (eqn entryLength typeLength))

/-- Every actual extracted member retains the original type annotation and is
accepted by the unchanged original term checker in the same context. The
observed pair is the original numeric pairing, not a native typed witness. -/
def InternalEntry : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (types raw gamma param entries entry tau child : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H types raw gamma)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) entries entry)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau child)) →
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.TermAccepted H tau child gamma))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.Targets
