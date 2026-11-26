module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransport (constant)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rowsAtFake (raw parameter row fake : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
 (hr : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows OriginalHereditaryExpansion.unpackJob) row fake parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply binaryRecover (OriginalHereditaryDeletionRows.rows OriginalHereditaryExpansion.unpackJob)
   (pairOf (constant 2 0) (.projection 0)) (.projection 1) row fake parameter xs hr
 · exact binaryValue InternalPairing.pairing (constant 2 0) (.projection 0) fake z raw xs hp
     (constantValue 0 xs) (projectionValue 0 xs)
 · exact projectionValue 1 xs

theorem contextLength (raw parameter row count fake window gamma actualCount : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
 (hl : Nonempty (Derivation body Delta (lengthGraph actualCount gamma)))
 (hr : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter)))
 (hout : Nonempty (Derivation body Delta (lengthGraph count row))) :
 Nonempty (Derivation body Delta (lengthGraph count gamma)) := by
 have hrows := rowsAtFake raw parameter row fake hf hr
 have hs := OriginalHereditaryDeletionRowsBoundProof.scanFromRows OriginalHereditaryExpansion.unpackJob
   fake parameter gamma actualCount row (pairRight parameter window gamma hp) hl hrows
 have hlen := OriginalHereditaryDeletionRowsScanLengthProof.scanLength OriginalHereditaryExpansion.unpackJob
   actualCount fake parameter row hs
 have he := valueUnique length actualCount count (Fin.cons row Fin.elim0) hlen hout
 exact outputTransport length actualCount count (Fin.cons gamma Fin.elim0) he hl

theorem childAtCoordinates (raw parameter row count cutoff child fake window gamma typ deleted erased childParameter packedErased : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
 (hb : Nonempty (Derivation body Delta (Below cutoff count)))
 (hr : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child cutoff row)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typ cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased typ cutoff raw)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter window deleted)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packedErased z erased))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child erased childParameter)) := by
 have hrows := rowsAtFake raw parameter row fake hf hr
 have ho := (OriginalHereditaryDeletionRowsSquareSupportProof.rowExpose OriginalHereditaryExpansion.unpackJob
   count fake parameter window gamma cutoff row child hp hl hb hrows hv).1
 let xs : Fin 3 → OTerm alpha := Fin.cons typ (Fin.cons cutoff (Fin.cons fake Fin.elim0))
 have hleft := unaryValue InternalUnpair.left (.projection 2) z fake xs
   (pairLeft fake z raw hf) (projectionValue 2 xs)
 have hright := unaryValue InternalUnpair.right (.projection 2) raw fake xs
   (pairRight fake z raw hf) (projectionValue 2 xs)
 have hrawErase := ternaryValue OriginalRawSyntaxTransport.eraseRaw (.projection 0) (.projection 1)
   (rightOf (.projection 2)) erased typ cutoff raw xs he (projectionValue 0 xs) (projectionValue 1 xs) hright
 have hpe : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw packedErased typ cutoff fake)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 2))
    (.composition OriginalRawSyntaxTransport.eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)])
    packedErased z erased xs hpacked hleft hrawErase
 have hselectors := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro
   cutoff fake parameter window gamma typ deleted packedErased childParameter hp ht hd hpe hcp
 let ys : Fin 3 → OTerm alpha := Fin.cons cutoff (Fin.cons fake (Fin.cons parameter Fin.elim0))
 have hunpack := binaryRecover OriginalHereditaryExpansion.unpackJob
   OriginalClassContextAllPositionObserver.erasedPacked OriginalClassContextAllPositionObserver.erasedParameter
   child packedErased childParameter ys ho hselectors.1 hselectors.2
 let zs : Fin 2 → OTerm alpha := Fin.cons packedErased (Fin.cons childParameter Fin.elim0)
 exact binaryRecover InternalPairing.pairing (rightOf (.projection 0)) (.projection 1)
   child erased childParameter zs hunpack
   (unaryValue InternalUnpair.right (.projection 0) erased packedErased zs
     (pairRight packedErased z erased hpacked) (projectionValue 0 zs))
   (projectionValue 1 zs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupSupportProof
