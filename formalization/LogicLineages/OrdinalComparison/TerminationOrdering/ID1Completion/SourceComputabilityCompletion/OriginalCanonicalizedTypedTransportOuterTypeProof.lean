module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportExposureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportOuterTypeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (pairLeft)
open InternalControlGraphSupportProof (valueUnique outputTransport)
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalRawSyntaxTransport
open OriginalTransparentDecoderFinalTransportExposureProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The raw payload and its actual shifted output are recovered internally.
Original graph functionality then preserves the requested outer type. -/
theorem shiftedLeft (input shifted typ cutoff : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted cutoff input)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ shifted)) := by
  apply shiftPackedCases input shifted cutoff _ hs
  intro beta j Theta recorded raw transformed hj hp _ hout
  rw [graph1Rename]
  have hl' := renameInto hl j Theta hj
  rw [graph1Rename] at hl'
  have he := valueUnique InternalUnpair.left recorded (typ.relabel j)
    (Fin.cons (input.relabel j) Fin.elim0)
    (pairLeft (input.relabel j) recorded raw hp) hl'
  exact outputTransport InternalUnpair.left recorded (typ.relabel j)
    (Fin.cons (shifted.relabel j) Fin.elim0) he
    (pairLeft (shifted.relabel j) recorded transformed hout)

/-- Erasure copies exactly the same outer type, regardless of the erased
type or context. No native decoding or canonicality is used. -/
theorem erasedLeft (input erased typ d cutoff : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d cutoff input)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ erased)) := by
  apply erasePackedCases input erased d cutoff _ he
  intro beta j Theta recorded raw transformed hj hp _ hout
  rw [graph1Rename]
  have hl' := renameInto hl j Theta hj
  rw [graph1Rename] at hl'
  have ht := valueUnique InternalUnpair.left recorded (typ.relabel j)
    (Fin.cons (input.relabel j) Fin.elim0)
    (pairLeft (input.relabel j) recorded raw hp) hl'
  exact outputTransport InternalUnpair.left recorded (typ.relabel j)
    (Fin.cons (erased.relabel j) Fin.elim0) ht
    (pairLeft (erased.relabel j) recorded transformed hout)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportOuterTypeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportOuterTypeProof
