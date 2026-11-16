module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem introduce {k : Nat} (tag : Nat) (payload : Program k) (xs : Fin k → OTerm alpha)
    (code value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph payload value xs)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationConstructorLayer.tagPayload tag) code value))) :
    Nonempty (Derivation body Delta (programGraph (pairOf (OriginalRawSyntaxTransport.constant k tag) payload) code xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 tag) (.projection 0)
    code (numeral tag) value ![value] ht (constantValue tag ![value]) (projectionValue 0 ![value])
  exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant k tag) payload
    code (numeral tag) value xs hpair (constantValue tag xs) hp

theorem recover {k : Nat} (tag : Nat) (payload : Program k) (xs : Fin k → OTerm alpha)
    (code value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph payload value xs)))
    (ht : Nonempty (Derivation body Delta (programGraph (pairOf (OriginalRawSyntaxTransport.constant k tag) payload) code xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalEnumerationConstructorLayer.tagPayload tag) code value)) := by
  have hpair := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant k tag) payload
    code (numeral tag) value xs ht (constantValue tag xs) hp
  exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 tag) (.projection 0)
    code (numeral tag) value ![value] hpair (constantValue tag ![value]) (projectionValue 0 ![value])

def binaryPayload : Program 2 := pairOf (.projection 0) (.projection 1)
def ternaryPayload : Program 3 := pairOf (.projection 0) (pairOf (.projection 1) (.projection 2))

theorem binaryAt (a b payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload a b))) :
    Nonempty (Derivation body Delta (graph2 binaryPayload payload a b)) :=
  binaryValue InternalPairing.pairing (.projection 0) (.projection 1) payload a b ![a,b]
    hp (projectionValue 0 ![a,b]) (projectionValue 1 ![a,b])

theorem ternaryAt (a b c inner payload : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner b c)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload a inner))) :
    Nonempty (Derivation body Delta (graph3 ternaryPayload payload a b c)) := by
  have hin : Nonempty (Derivation body Delta
      (programGraph (pairOf (.projection 1) (.projection 2)) inner ![a,b,c])) :=
    binaryValue InternalPairing.pairing (.projection 1) (.projection 2) inner b c ![a,b,c]
      hi (projectionValue 1 ![a,b,c]) (projectionValue 2 ![a,b,c])
  exact binaryValue InternalPairing.pairing (.projection 0) (pairOf (.projection 1) (.projection 2))
    payload a inner ![a,b,c] hp (projectionValue 0 ![a,b,c]) hin
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
