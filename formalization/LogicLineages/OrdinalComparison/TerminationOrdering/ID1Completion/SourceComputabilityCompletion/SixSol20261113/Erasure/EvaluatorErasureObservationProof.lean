module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof (projectionValue)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Open the actual original hereditary row observation at literal erase and
parameter-selector graphs. The output is unchanged, not reconstructed natively. -/
theorem actualCell (Q : Program 2)
 (input erased parameter newParameter c gamma deleted cutoff d value : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParameter c deleted)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased d cutoff input)))
 (ho : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter))) :
 Nonempty (Derivation body Delta (graph2 Q value erased newParameter)) := by
 let xs : Fin 3 → OTerm alpha := ![cutoff,input,parameter]
 let leftP : Program 3 := leftOf (.projection 2)
 let rightP : Program 3 := rightOf (.projection 2)
 let lookupP : Program 3 := .composition InternalRawListRecursion.lookup ![.projection 0,rightP]
 let deletedP : Program 3 := .composition deleteAt ![.projection 0,rightP]
 have hleft := unaryValue InternalUnpair.left (.projection 2) c parameter xs
   (pairLeft parameter c gamma hp) (projectionValue 2 xs)
 have hright := unaryValue InternalUnpair.right (.projection 2) gamma parameter xs
   (pairRight parameter c gamma hp) (projectionValue 2 xs)
 have hlookup := binaryValue InternalRawListRecursion.lookup (.projection 0) rightP d cutoff gamma xs
   hl (projectionValue 0 xs) hright
 have hdeleted := binaryValue deleteAt (.projection 0) rightP deleted cutoff gamma xs
   hd (projectionValue 0 xs) hright
 have herased := ternaryValue OriginalRawSyntaxTransport.erasePackedRaw lookupP (.projection 0) (.projection 1)
   erased d cutoff input xs he hlookup (projectionValue 0 xs) (projectionValue 1 xs)
 have hnew := binaryValue InternalPairing.pairing leftP deletedP newParameter c deleted xs hn hleft hdeleted
 exact binaryRecover Q erasedPacked erasedParameter value erased newParameter xs ho herased hnew
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
