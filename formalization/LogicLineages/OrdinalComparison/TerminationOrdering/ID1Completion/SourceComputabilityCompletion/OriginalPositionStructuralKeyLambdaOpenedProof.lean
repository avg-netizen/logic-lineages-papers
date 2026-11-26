module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationOpenedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaOpenedProof
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
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open OriginalPositionStructuralKeyOpeningDefinitions OriginalPositionStructuralKeyOpeningSupportProof
open OriginalPositionStructuralKeyObserverWiringProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalClassContextAllPositionObserver
open UniformCertificateCompletion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atOpened (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out d e child childOut parameter childParameter cutoff childMark mark context gamma erasedType deleted outE erasedParam keyValue rank : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)))
 (hsc : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) child childParameter)))
 (hsco : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) childOut childParameter)))
 (hfi : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input d e child parameter childParameter)))
 (hfo : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields out d e childOut parameter childParameter)))
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (hout : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hoc : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) childMark (suc cutoff) child childParameter)))
 (hoco : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) childMark (suc cutoff) childOut childParameter)))
 (opened : Nonempty (Derivation body Delta (Opened p H G W out parameter cutoff mark context gamma erasedType deleted outE erasedParam keyValue rank)))
 :
 Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff input parameter)) := by
 let R := OriginalStructuralClassKeyDefinitions.key p H G W
 let oldExt : Program 9 := consOf (.projection 0) (.projection 1)
 let newExt : Program 9 := consOf (.projection 0) (.projection 2)
 let childParam : Program 9 := pairOf (.projection 3) newExt
 let nextCut : Program 9 := .composition .succ (fun _ : Fin 1 => .projection 4)
 let parentErase : Program 9 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![.projection 5,.projection 4,.projection 6]
 let E (i : Fin 9) : Program 9 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![.projection 5,nextCut,.projection i]
 let RK (i : Fin 9) : Program 9 := .composition R ![E i,childParam]
 let RR (i : Fin 9) : Program 9 := .composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => E i)
 let qs : Fin 10 → Program 9 := ![oldExt,newExt,childParam,parentErase,E 7,E 8,RK 7,RK 8,RR 7,RR 8]
 let xs : Fin 9 → OTerm alpha := ![d,gamma,deleted,context,cutoff,erasedType,input,child,childOut]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 rw [graph3Rename]
 have hw := renameInto hw j Theta hj
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hw
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hs
 have ho := renameInto ho j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at ho
 have hsc := renameInto hsc j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hsc
 have hsco := renameInto hsco j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hsco
 have hfi := renameInto hfi j Theta hj
 simp only [OriginalLambdaTraversalInternalFieldsSyntaxProof.lambdaFieldsRename] at hfi
 have hfo := renameInto hfo j Theta hj
 simp only [OriginalLambdaTraversalInternalFieldsSyntaxProof.lambdaFieldsRename] at hfo
 have hi := renameInto hi j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hi
 have hout := renameInto hout j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hout
 have hoc := renameInto hoc j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hoc
 have hoco := renameInto hoco j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hoco
 have opened := renameInto opened j Theta hj
 simp only [OriginalPositionStructuralKeyApplicationOpenedProof.openedRename] at opened
 let input := input.relabel j
 let out := out.relabel j
 let d := d.relabel j
 let e := e.relabel j
 let child := child.relabel j
 let childOut := childOut.relabel j
 let parameter := parameter.relabel j
 let childParameter := childParameter.relabel j
 let cutoff := cutoff.relabel j
 let childMark := childMark.relabel j
 let mark := mark.relabel j
 let context := context.relabel j
 let gamma := gamma.relabel j
 let erasedType := erasedType.relabel j
 let deleted := deleted.relabel j
 let outE := outE.relabel j
 let erasedParam := erasedParam.relabel j
 let keyValue := keyValue.relabel j
 let rank := rank.relabel j
 let xx : Fin 9 → OTerm beta := ![d,gamma,deleted,context,cutoff,erasedType,input,child,childOut]
 have hxs : (fun a => (xs a).relabel j) = xx := by
   funext a
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl ((fun k => Fin.elim0 k)))))))))) a
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [hxs] using hq i
 have oldCons := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1) (ys 0) d gamma xx (hq' 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have newCons := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 2) (ys 1) d deleted xx (hq' 1) (projectionValue 0 xx) (projectionValue 2 xx)
 have newPair := binaryRecover InternalPairing.pairing (.projection 3) newExt (ys 2) context (ys 1) xx (hq' 2) (projectionValue 3 xx) (hq' 1)
 have nextValue : Nonempty (Derivation body Theta (programGraph nextCut (suc cutoff) xx)) := by
   exact unaryValue .succ (.projection 4) (suc cutoff) cutoff xx
     (successorValue (Fin.cons cutoff Fin.elim0)) (projectionValue 4 xx)
 have erInput := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 5) (.projection 4) (.projection 6)
   (ys 3) erasedType cutoff input xx (hq' 3) (projectionValue 5 xx) (projectionValue 4 xx) (projectionValue 6 xx)
 have erChild := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 5) nextCut (.projection 7)
   (ys 4) erasedType (suc cutoff) child xx (hq' 4) (projectionValue 5 xx) nextValue (projectionValue 7 xx)
 have erOther := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 5) nextCut (.projection 8)
   (ys 5) erasedType (suc cutoff) childOut xx (hq' 5) (projectionValue 5 xx) nextValue (projectionValue 8 xx)
 have kc := binaryRecover R (E 7) childParam (ys 6) (ys 4) (ys 2) xx (hq' 6) (hq' 4) (hq' 2)
 have ko := binaryRecover R (E 8) childParam (ys 7) (ys 5) (ys 2) xx (hq' 7) (hq' 5) (hq' 2)
 have rc := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (E 7) (ys 8) (ys 4) xx (hq' 8) (hq' 4)
 have ro := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (E 8) (ys 9) (ys 5) xx (hq' 9) (hq' 5)
 have hp := andLeft opened
 have hl := andLeft (andRight opened)
 have hd := andLeft (andRight (andRight opened))
 have hins := andLeft (andRight (andRight (andRight opened)))
 have erOut := andLeft (andRight (andRight (andRight (andRight opened))))
 have hep := andLeft (andRight (andRight (andRight (andRight (andRight opened)))))
 have keyOut := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened)))))))))
 have rankOut := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened))))))))))
 have pairMark := (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened)))))))))))
 have oldPair := OriginalPositionStructuralKeyLambdaContextProof.childPair input d e child parameter childParameter context gamma (ys 0) hfi hp oldCons
 have childInsert := OriginalContextInsertionConsProof.consBackward erasedType cutoff (ys 1) (ys 0) d deleted gamma newCons oldCons hins
 have gi := OriginalPositionStructuralKeyLambdaGeometryProof.erasedFields input (ys 3) child (ys 4) d e parameter childParameter erasedType cutoff context deleted gamma erasedParam (ys 1) (ys 2) hfi hi erInput erChild hins hep newCons newPair
 have go := OriginalPositionStructuralKeyLambdaGeometryProof.erasedFields out outE childOut (ys 5) d e parameter childParameter erasedType cutoff context deleted gamma erasedParam (ys 1) (ys 2) hfo hout erOut erOther hins hep newCons newPair
 exact OriginalPositionStructuralKeyLambdaCoordinatesProof.atCoordinates p H G W
   input out d e child childOut parameter childParameter cutoff childMark mark context gamma deleted
   (ys 0) (ys 1) erasedType (ys 3) outE (ys 4) (ys 5) erasedParam (ys 2) (ys 6) (ys 7) (ys 8) (ys 9) keyValue rank
   hw hs ho hsc hsco hp oldPair hep newPair oldCons newCons hl hd hins childInsert
   erInput erOut erChild erOther (andLeft gi) (andLeft go) (andRight gi) (andRight go) kc ko rc ro rankOut keyOut hoc hoco pairMark

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaOpenedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaOpenedProof
