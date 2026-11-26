module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- The SAME in-range index into actual extracted entries and accepted argument
types yields the same annotation, and the observed child satisfies the original
term checker at that positional type. Lookup's out-of-range zero is not a member. -/
def InternalPosition : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (types raw gamma param entries count index entry annotation child expected : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H types raw gamma)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count types)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup entry index entries)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup expected index types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry annotation child)) →
  Nonempty (Derivation body Delta (eqn annotation expected ⊓
    OriginalTypedDecoderInternalAcceptance.TermAccepted H expected child gamma))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.Targets
