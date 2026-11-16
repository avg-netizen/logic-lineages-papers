module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PayloadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambdaCode (raw metadata child payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload metadata child))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)) := by
  let xs : Fin 2 → OTerm alpha := ![metadata,child]
  have hinner := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    payload metadata child xs hp (projectionValue 0 xs) (projectionValue 1 xs)
  exact binaryRecover InternalPairing.pairing (constant 2 1) (pairOf (.projection 0) (.projection 1))
    raw (numeral 1) payload xs hc (constantValue 1 xs) hinner

theorem ordinary (raw metadata child payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw metadata child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload metadata child))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) := by
  let xs : Fin 2 → OTerm alpha := ![metadata,child]
  have hinner := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    payload metadata child xs hp (projectionValue 0 xs) (projectionValue 1 xs)
  exact binaryRecover InternalPairing.pairing (constant 2 4) (pairOf (.projection 0) (.projection 1))
    raw (numeral 4) payload xs hc (constantValue 4 xs) hinner
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PayloadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PayloadProof
