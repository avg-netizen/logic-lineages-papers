module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalLeafParametersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParameters
open OriginalRawSyntaxTransportInternalLeafParametersProof
open OriginalRawSyntaxTransportInternalFoldLeafProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The induction leaf case holds on all zero-arity raw values, including
unknown tags and malformed tag-six payloads. -/
theorem leafParameters (rank : Bool) (raw out d k other otherK : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (h : Nonempty (Derivation body Delta (graph3 (fold (selectedMode rank)) out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode rank)) out other (if rank then otherK else k) raw)) := by
  cases rank with
  | false =>
    exact leafBackward .shift other k raw out ha
      (shiftLeafParameters out d other k raw (leafForward .shift d k raw out ha h))
  | true =>
    exact leafBackward .rank other otherK raw out ha
      (rankLeafParameters out d k other otherK raw (leafForward .rank d k raw out ha h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersLeafProof
