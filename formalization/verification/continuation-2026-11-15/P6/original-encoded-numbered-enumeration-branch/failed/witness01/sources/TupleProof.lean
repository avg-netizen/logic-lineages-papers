module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.TupleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def pair56 : Program 6 := pairOf (.projection 4) (.projection 5)
def pair456 : Program 6 := pairOf (.projection 3) pair56
def pair3456 : Program 6 := pairOf (.projection 2) pair456
def pair23456 : Program 6 := pairOf (.projection 1) pair3456
def pair123456 : Program 6 := pairOf (.projection 0) pair23456

theorem payloadAt (k h t b ts e p56 p456 p3456 p23456 payload : OTerm alpha)
    (hp56 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p56 ts e)))
    (hp456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p456 b p56)))
    (hp3456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3456 t p456)))
    (hp23456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p23456 h p3456)))
    (hp123456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload k p23456))) :
    Nonempty (Derivation body Delta (programGraph pair123456 payload ![k,h,t,b,ts,e])) := by
  let xs : Fin 6 → OTerm alpha := ![k,h,t,b,ts,e]
  have hv56 : Nonempty (Derivation body Delta (programGraph pair56 p56 xs)) :=
    binaryValue InternalPairing.pairing (.projection 4) (.projection 5) p56 ts e xs hp56
      (projectionValue 4 xs) (projectionValue 5 xs)
  have hv456 : Nonempty (Derivation body Delta (programGraph pair456 p456 xs)) :=
    binaryValue InternalPairing.pairing (.projection 3) pair56 p456 b p56 xs hp456
      (projectionValue 3 xs) hv56
  have hv3456 : Nonempty (Derivation body Delta (programGraph pair3456 p3456 xs)) :=
    binaryValue InternalPairing.pairing (.projection 2) pair456 p3456 t p456 xs hp3456
      (projectionValue 2 xs) hv456
  have hv23456 : Nonempty (Derivation body Delta (programGraph pair23456 p23456 xs)) :=
    binaryValue InternalPairing.pairing (.projection 1) pair3456 p23456 h p3456 xs hp23456
      (projectionValue 1 xs) hv3456
  exact binaryValue InternalPairing.pairing (.projection 0) pair23456 payload k p23456 xs hp123456
    (projectionValue 0 xs) hv23456

theorem constructorValue (k h t b ts e payload code : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph pair123456 payload ![k,h,t,b,ts,e])))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code (numeral 5) payload))) :
    Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,h,t,b,ts,e])) :=
  binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 6 5) pair123456
    code (numeral 5) payload ![k,h,t,b,ts,e] hc (constantValue 5 ![k,h,t,b,ts,e]) hp

theorem constructorRecover (k h t b ts e payload code : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph pair123456 payload ![k,h,t,b,ts,e])))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,h,t,b,ts,e]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code (numeral 5) payload)) :=
  binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 6 5) pair123456
    code (numeral 5) payload ![k,h,t,b,ts,e] hc (constantValue 5 ![k,h,t,b,ts,e]) hp

theorem tagValue (payload code : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code (numeral 5) payload))) :
    Nonempty (Derivation body Delta (graph1 OriginalNumberedEnumerationBranch.tagPayload code payload)) :=
  binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 5) (.projection 0)
    code (numeral 5) payload ![payload] hc (constantValue 5 ![payload]) (projectionValue 0 ![payload])

theorem tagRecover (payload code : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalNumberedEnumerationBranch.tagPayload code payload))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code (numeral 5) payload)) :=
  binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 5) (.projection 0)
    code (numeral 5) payload ![payload] hc (constantValue 5 ![payload]) (projectionValue 0 ![payload])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.TupleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.TupleProof
