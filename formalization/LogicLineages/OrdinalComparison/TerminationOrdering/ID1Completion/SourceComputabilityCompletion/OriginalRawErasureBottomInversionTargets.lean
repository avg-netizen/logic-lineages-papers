module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
/-- Allraw inversion: a nonvariable original root can erase to bottom-tag
only by remaining literally unchanged. No source validity or native premise. -/
def ActualBottomInversion : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw out erasedType cutoff tag : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 rawTag tag raw)) →
 Nonempty (Derivation body Delta (equal tag (numeral 0)).not) →
 Nonempty (Derivation body Delta (graph3 eraseRaw out erasedType cutoff raw)) →
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 3) out)) →
 Nonempty (Derivation body Delta (equal out raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionTargets
