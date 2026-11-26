module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- All six fields are copied into the ORIGINAL numbered constructor in order:
label, head, result type, base child, type-list number, extras child. -/
theorem numberedConstructorValue
    (raw p1 p2 p3 p4 p5 label head tau base types extras : OTerm alpha)
    (h0 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing raw (numeral 5) p1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p1 label p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 head p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 tau p4)))
    (h4 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p4 base p5)))
    (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p5 types extras))) :
    Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])) := by
  let xs : Fin 6 → OTerm alpha := ![label,head,tau,base,types,extras]
  have v5 : Nonempty (Derivation body Delta
      (programGraph (pairOf (.projection 4) (.projection 5)) p5 xs)) :=
    binaryValue InternalPairing.pairing (.projection 4) (.projection 5)
      p5 types extras xs h5 (projectionValue 4 xs) (projectionValue 5 xs)
  have v4 : Nonempty (Derivation body Delta
      (programGraph (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5))) p4 xs)) :=
    binaryValue InternalPairing.pairing (.projection 3) (pairOf (.projection 4) (.projection 5))
      p4 base p5 xs h4 (projectionValue 3 xs) v5
  have v3 : Nonempty (Derivation body Delta
      (programGraph (pairOf (.projection 2)
        (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))) p3 xs)) :=
    binaryValue InternalPairing.pairing (.projection 2)
      (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))
      p3 tau p4 xs h3 (projectionValue 2 xs) v4
  have v2 : Nonempty (Derivation body Delta
      (programGraph (pairOf (.projection 1) (pairOf (.projection 2)
        (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5))))) p2 xs)) :=
    binaryValue InternalPairing.pairing (.projection 1) (pairOf (.projection 2)
      (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5))))
      p2 head p3 xs h2 (projectionValue 1 xs) v3
  have v1 : Nonempty (Derivation body Delta
      (programGraph (pairOf (.projection 0) (pairOf (.projection 1) (pairOf (.projection 2)
        (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))))) p1 xs)) :=
    binaryValue InternalPairing.pairing (.projection 0) (pairOf (.projection 1)
      (pairOf (.projection 2) (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))))
      p1 label p2 xs h1 (projectionValue 0 xs) v2
  exact binaryValue InternalPairing.pairing (constant 6 5)
    (pairOf (.projection 0) (pairOf (.projection 1) (pairOf (.projection 2)
      (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5))))))
    raw (numeral 5) p1 xs h0 (constantValue 5 xs) v1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedValueProof
