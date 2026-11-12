module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOldKeyCancellationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalPackedCancellationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOldKeyCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors
open OriginalAllPositionStructuralTraversalDefinitions
open OriginalPositionStructuralKeyOpeningDefinitions
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffBackward)
open OriginalPositionStructuralKeyObserverWiringProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atValues (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (law : OriginalAllPositionStructuralTraversalTargets.FinalLaw p H G W P)
 (input shifted out erased typ parameter insertedParameter context gamma extended erasedType cutoff keyValue rank afterKey afterRank mark : OTerm alpha)
 (hfinal : Nonempty (Derivation body Delta ((OriginalFunctionNeutrality.windowGraph (OriginalLambdaTraversalSelection.finalInputs (refined p H G W P)).window shifted insertedParameter ⊓ (InternalParameterizedCanonicalResultFold.sourcePremises (OriginalLambdaTraversalSelection.finalData (refined p H G W P)) shifted typ insertedParameter ⊓ InternalParameterizedCanonicalResultFold.foldGraph (OriginalLambdaTraversalSelection.finalData (refined p H G W P)) out shifted insertedParameter)))))
 (hrange : Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff insertedParameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hip : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing insertedParameter context extended)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff extended)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt gamma cutoff extended)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.shiftPackedRaw shifted cutoff input)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased erasedType cutoff out)))
 (hk : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) keyValue input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (hak : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) afterKey erased parameter)))
 (har : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw afterRank erased)))
 (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark keyValue rank))) :
 Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) keyValue erased parameter ⊓ graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased)) := by
 let K := OriginalStructuralClassKeyDefinitions.key p H G W
 have inverse := OriginalRawObjectTransportInternalPackedCancellationProof.packedRightInverse input shifted erasedType cutoff hs
 have oldObservation := positionBackward K cutoff shifted insertedParameter context extended erasedType gamma input parameter keyValue rank mark hip hl hd inverse hp hk hr hm
 obtain ⟨rule⟩ := law body alpha Delta out shifted typ insertedParameter mark cutoff
 obtain ⟨args⟩ := andIntro hfinal hrange
 have comparison := Nonempty.intro (Derivation.implicationElimination rule args)
 have newObservation := iffBackward comparison oldObservation
 have newPair := positionForward K cutoff out insertedParameter context extended erasedType gamma erased parameter afterKey afterRank mark hip hl hd he hp hak har newObservation
 have shared := OriginalPositionStructuralKeyApplicationCoreProof.sharedPairValues K mark keyValue rank afterKey afterRank erased parameter hm newPair hak har
 exact andIntro shared.1 shared.2

/-- Proof-side staging only: the frozen cancellation target adds no law
premise. Specialize this theorem once the actual whole-final gate is checked. -/
theorem fromFinal (law : OriginalAllPositionStructuralTraversalTargets.ActualFinal) :
 OriginalAllPositionOldKeyCancellationTargets.ActualCancellation := by
 intro p H G W P body alpha Delta input shifted out erased typ parameter insertedParameter context gamma extended erasedType cutoff keyValue rank
   hfinal hrange hp hip hl hd hs he hk hr
 let K := OriginalStructuralClassKeyDefinitions.key p H G W
 let qs : Fin 3 → Program 4 :=
   ![.composition K ![.projection 0,.projection 1],
     .composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => .projection 0),
     pairOf (.projection 2) (.projection 3)]
 let xs : Fin 4 → OTerm alpha := ![erased,parameter,keyValue,rank]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [conjunctionRename,graph1Rename,graph2Rename]
 have hfinal := renameInto hfinal j Theta hj
 simp only [conjunctionRename,OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename,InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename,graph2Rename,InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hfinal
 have hrange := renameInto hrange j Theta hj
 simp only [OriginalIndexedObserverRangeSyntaxProof.rangeRename] at hrange
 have hp := renameInto hp j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hp
 have hip := renameInto hip j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hip
 have hl := renameInto hl j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hl
 have hd := renameInto hd j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hd
 have hs := renameInto hs j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hs
 have he := renameInto he j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at he
 have hk := renameInto hk j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hk
 have hr := renameInto hr j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename] at hr
 let input := input.relabel j
 let shifted := shifted.relabel j
 let out := out.relabel j
 let erased := erased.relabel j
 let typ := typ.relabel j
 let parameter := parameter.relabel j
 let insertedParameter := insertedParameter.relabel j
 let context := context.relabel j
 let gamma := gamma.relabel j
 let extended := extended.relabel j
 let erasedType := erasedType.relabel j
 let cutoff := cutoff.relabel j
 let keyValue := keyValue.relabel j
 let rank := rank.relabel j
 let xx : Fin 4 → OTerm beta := ![erased,parameter,keyValue,rank]
 have hxs : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [hxs] using hq i
 have hak := binaryRecover K (.projection 0) (.projection 1) (ys 0) erased parameter xx (hq' 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have har := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (.projection 0) (ys 1) erased xx (hq' 1) (projectionValue 0 xx)
 have hm := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3) (ys 2) keyValue rank xx (hq' 2) (projectionValue 2 xx) (projectionValue 3 xx)
 exact atValues p H G W P (law p H G W P)
   input shifted out erased typ parameter insertedParameter context gamma extended erasedType cutoff keyValue rank (ys 0) (ys 1) (ys 2)
   hfinal hrange hp hip hl hd hs he hk hr hak har hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOldKeyCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOldKeyCancellationProof
