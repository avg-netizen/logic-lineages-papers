module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.RowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CrossProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open Continuation20261114 NumericDependencyCross
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem crossFour (q a r b lefts leftTail rights rightTail qr qb ar ab deps d1 d2 d3 row0 rowTail : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts q leftTail)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights r rightTail)))
    (hrt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rightTail b z)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hrow0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row0 qr rowTail)))
    (hrow1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rowTail qb z)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    : Nonempty (Derivation body Delta (graph2 cross deps lefts rights)) := by
  have hr0 := RowsProof.rowTwo q r b rights rightTail qr qb rowTail row0 hr hrt hp0 hp1 hrow0 hrow1
  have hr1 := RowsProof.rowTwo a r b rights rightTail ar ab d3 d2 hr hrt hp2 hp3 h2 h3
  have hz := InternalRawListRecursionProof.nilValue (body := body) (Gamma := Delta)
    (InternalAcceptance.constantZero 1) crossStep z (Fin.cons rights Fin.elim0)
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons rights Fin.elim0))
  have ht := RowsProof.crossCons leftTail a z rights d2 z d2 hlt hz hr1
    (RowsProof.appendTwo d2 ar d3 ab z d2 d3 h2 h3 h2 h3)
  exact RowsProof.crossCons lefts q leftTail rights row0 d2 deps hl ht hr0
    (RowsProof.appendTwo row0 qr rowTail qb d2 deps d1 hrow0 hrow1 h0 h1)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CrossProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CrossProof
