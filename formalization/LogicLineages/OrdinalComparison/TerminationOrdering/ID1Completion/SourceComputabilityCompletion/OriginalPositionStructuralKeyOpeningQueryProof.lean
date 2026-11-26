module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open UniformCertificateCompletion OriginalPositionStructuralKeyOpeningDefinitions
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof-side staging: the deletion theorem is supplied by its independent
arithmetic proof, not by any premise of ActualOpening. -/
theorem atCount (deletion : OriginalAllPositionContextDeleteTargets.ActualDeletionInsertion)
 (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (value parameter cutoff mark count : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) value parameter)))
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window value parameter)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalIndexedObserverDefinitions.contextLength count parameter)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (ho : Nonempty (Derivation body Delta
   (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff value parameter)))
 (consume : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (context gamma erasedType deleted erased erasedParam keyValue rank : OTerm beta),
   (∀ h ∈ Delta, h.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (Opened p H G W (value.relabel j) (parameter.relabel j)
     (cutoff.relabel j) (mark.relabel j) context gamma erasedType deleted erased erasedParam keyValue rank)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let R := OriginalStructuralClassKeyDefinitions.key p H G W
 let lookupAt : Program 3 := .composition InternalRawListRecursion.lookup ![.projection 0,rightOf (.projection 2)]
 let deleteAtParam : Program 3 := .composition deleteAt ![.projection 0,rightOf (.projection 2)]
 let keyAt : Program 3 := .composition R ![erasedPacked,erasedParameter]
 let rankAt : Program 3 := .composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => erasedPacked)
 let qs : Fin 8 → Program 3 := ![leftOf (.projection 2),rightOf (.projection 2),lookupAt,deleteAtParam,
   erasedPacked,erasedParameter,keyAt,rankAt]
 let xs : Fin 3 → OTerm alpha := Fin.cons cutoff (Fin.cons value (Fin.cons parameter Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 3 → OTerm beta := Fin.cons (cutoff.relabel j)
   (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [xs,xx,consTermRename,emptyRename] using hq i
 have hleft := unaryRecover InternalUnpair.left (.projection 2) (ys 0) (parameter.relabel j) xx
   (hq' 0) (projectionValue 2 xx)
 have hright := unaryRecover InternalUnpair.right (.projection 2) (ys 1) (parameter.relabel j) xx
   (hq' 1) (projectionValue 2 xx)
 have hp := reconstructPair (parameter.relabel j) (ys 0) (ys 1) hleft hright
 have hlookup := binaryRecover InternalRawListRecursion.lookup (.projection 0) (rightOf (.projection 2))
   (ys 2) (cutoff.relabel j) (ys 1) xx (hq' 2) (projectionValue 0 xx) (hq' 1)
 have hdelete := binaryRecover deleteAt (.projection 0) (rightOf (.projection 2))
   (ys 3) (cutoff.relabel j) (ys 1) xx (hq' 3) (projectionValue 0 xx) (hq' 1)
 have herase := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw lookupAt (.projection 0) (.projection 1)
   (ys 4) (ys 2) (cutoff.relabel j) (value.relabel j) xx (hq' 4) (hq' 2)
   (projectionValue 0 xx) (projectionValue 1 xx)
 have heparam := binaryRecover InternalPairing.pairing (leftOf (.projection 2)) deleteAtParam
   (ys 5) (ys 0) (ys 3) xx (hq' 5) (hq' 0) (hq' 3)
 have hkey := binaryRecover R erasedPacked erasedParameter (ys 6) (ys 4) (ys 5) xx
   (hq' 6) (hq' 4) (hq' 5)
 have hrank := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw erasedPacked
   (ys 7) (ys 4) xx (hq' 7) (hq' 4)
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 have hpair := binaryRecover InternalPairing.pairing keyAt rankAt (mark.relabel j) (ys 6) (ys 7) xx
   ho' (hq' 6) (hq' 7)
 have hl' := renameInto hl j Theta hj
 rw [graph1Rename] at hl'
 have hlength := unaryRecover OriginalContextInsertion.length InternalUnpair.right
   (count.relabel j) (ys 1) (Fin.cons (parameter.relabel j) Fin.elim0) hl' hright
 have hb' := renameInto hb j Theta hj
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at hb'
 obtain ⟨del⟩ := deletion body beta Theta (count.relabel j) (ys 1) (cutoff.relabel j) (ys 3) (ys 2)
 obtain ⟨dp⟩ := andIntro hlength (andIntro hb' (andIntro hdelete hlookup))
 have hinsert : Nonempty (Derivation body Theta (OriginalContextInsertion.Insert (ys 2) (cutoff.relabel j) (ys 3) (ys 1))) :=
   ⟨Derivation.implicationElimination del dp⟩
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs'
 have hw' := renameInto hw j Theta hj
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
   graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
 have domain := OriginalPositionStructuralKeyOpeningSupportProof.erasedActiveAtCoordinates p H G W
   (value.relabel j) (parameter.relabel j) (ys 4) (ys 5) (ys 2) (cutoff.relabel j) (ys 0) (ys 1) (ys 3)
   hp heparam hinsert herase hs' hw'
 exact consume beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hj
   (andIntro hp (andIntro hlookup (andIntro hdelete (andIntro hinsert (andIntro herase
    (andIntro heparam (andIntro domain.1 (andIntro domain.2.1 (andIntro domain.2.2
     (andIntro hkey (andIntro hrank hpair)))))))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningQueryProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningQueryProof
