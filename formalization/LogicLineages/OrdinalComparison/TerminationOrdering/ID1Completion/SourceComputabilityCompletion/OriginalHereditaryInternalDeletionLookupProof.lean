module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransport (constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem actualLookup : OriginalHereditaryInternalDeletionLookupTargets.ActualLookup := by
 intro body alpha Delta raw parameter row count cutoff child psi hr hl hb hv next
 let fake : Program 3 := pairOf (constant 3 0) (.projection 0)
 let window : Program 3 := leftOf (.projection 1)
 let gamma : Program 3 := rightOf (.projection 1)
 let size : Program 3 := .composition length (fun _ : Fin 1 => gamma)
 let typ : Program 3 := .composition InternalRawListRecursion.lookup ![.projection 2,gamma]
 let deleted : Program 3 := .composition OriginalClassContextAllPositionObserver.deleteAt ![.projection 2,gamma]
 let erased : Program 3 := .composition OriginalRawSyntaxTransport.eraseRaw ![typ,.projection 2,.projection 0]
 let childParameter : Program 3 := pairOf window deleted
 let packed : Program 3 := pairOf (constant 3 0) erased
 let qs : Fin 9 → Program 3 := ![fake,window,gamma,size,typ,deleted,erased,childParameter,packed]
 let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons parameter (Fin.cons cutoff Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 3 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) (Fin.cons (cutoff.relabel j) Fin.elim0))
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
  intro i
  simpa only [xs,xx,consTermRename,emptyRename] using hq i
 have hfake := binaryRecover InternalPairing.pairing (constant 3 0) (.projection 0)
   (ys 0) z (raw.relabel j) xx (hq' 0) (constantValue 0 xx) (projectionValue 0 xx)
 have hw := unaryRecover InternalUnpair.left (.projection 1) (ys 1) (parameter.relabel j) xx (hq' 1) (projectionValue 1 xx)
 have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 2) (parameter.relabel j) xx (hq' 2) (projectionValue 1 xx)
 have hp := reconstructPair (parameter.relabel j) (ys 1) (ys 2) hw hg
 have hlen := unaryRecover length gamma (ys 3) (ys 2) xx (hq' 3) (hq' 2)
 have ht := binaryRecover InternalRawListRecursion.lookup (.projection 2) gamma
   (ys 4) (cutoff.relabel j) (ys 2) xx (hq' 4) (projectionValue 2 xx) (hq' 2)
 have hd := binaryRecover OriginalClassContextAllPositionObserver.deleteAt (.projection 2) gamma
   (ys 5) (cutoff.relabel j) (ys 2) xx (hq' 5) (projectionValue 2 xx) (hq' 2)
 have he := ternaryRecover OriginalRawSyntaxTransport.eraseRaw typ (.projection 2) (.projection 0)
   (ys 6) (ys 4) (cutoff.relabel j) (raw.relabel j) xx (hq' 6) (hq' 4)
   (projectionValue 2 xx) (projectionValue 0 xx)
 have hcp := binaryRecover InternalPairing.pairing window deleted (ys 7) (ys 1) (ys 5) xx (hq' 7) (hq' 1) (hq' 5)
 have hpacked := binaryRecover InternalPairing.pairing (constant 3 0) erased (ys 8) z (ys 6) xx (hq' 8) (constantValue 0 xx) (hq' 6)
 have hr' := renameInto hr j Theta hj
 rw [graph2Rename] at hr'
 have hl' := renameInto hl j Theta hj
 rw [lengthRename] at hl'
 have hb' := renameInto hb j Theta hj
 simp only [Below,InternalOriginalOrderSyntaxProof.orderRename] at hb'
 have hv' := renameInto hv j Theta hj
 rw [graph2Rename] at hv'
 have hlength := OriginalHereditaryInternalDeletionLookupSupportProof.contextLength
   (raw.relabel j) (parameter.relabel j) (row.relabel j) (count.relabel j)
   (ys 0) (ys 1) (ys 2) (ys 3) hp hfake hlen hr' hl'
 have hchild := OriginalHereditaryInternalDeletionLookupSupportProof.childAtCoordinates
   (raw.relabel j) (parameter.relabel j) (row.relabel j) (count.relabel j) (cutoff.relabel j) (child.relabel j)
   (ys 0) (ys 1) (ys 2) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8)
   hp hfake hlength hb' hr' hv' ht hd he hcp hpacked
 exact next beta j Theta (ys 1) (ys 2) (ys 4) (ys 5) (ys 6) (ys 7) hj
   hp hlength hb' ht hd he hcp hchild
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
