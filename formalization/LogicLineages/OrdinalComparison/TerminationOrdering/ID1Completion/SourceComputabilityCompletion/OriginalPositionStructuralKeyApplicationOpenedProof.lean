module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationOpenedProof
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
open OriginalPositionStructuralKeyObserverWiringProof OriginalPositionStructuralKeyApplicationCoreProof
open OriginalClassContextAllPositionObserver
open UniformCertificateCompletion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem openedRename {beta : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (value parameter cutoff mark context gamma erasedType deleted erased erasedParam keyValue rank : OTerm alpha)
 (j : alpha → beta) :
 (Opened p H G W value parameter cutoff mark context gamma erasedType deleted erased erasedParam keyValue rank).relabel j =
 Opened p H G W (value.relabel j) (parameter.relabel j) (cutoff.relabel j) (mark.relabel j)
  (context.relabel j) (gamma.relabel j) (erasedType.relabel j) (deleted.relabel j)
  (erased.relabel j) (erasedParam.relabel j) (keyValue.relabel j) (rank.relabel j) := by
 simp only [Opened,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,
   OriginalContextInsertionSyntaxProof.insertRename,GuardedSourceSyntaxProof.numeralRename,
   OriginalStructuralClassKeyDefinitions.Active,OriginalFunctionNeutrality.windowGraph,
   OriginalVariableRepresentative.windowGraph,InternalOriginalStepGuard.one,
   InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]

theorem atOpened (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out domain codomain arrow fn arg fnOut argOut parameter cutoff fMark aMark mark context gamma erasedType deleted outE erasedParam keyValue rank : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)))
 (hsf : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) fn parameter)))
 (hsa : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) arg parameter)))
 (hsfo : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) fnOut parameter)))
 (hsao : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) argOut parameter)))
 (harr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain codomain)))
 (htf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)))
 (htfo : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fnOut)))
 (hta : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain arg)))
 (htao : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain argOut)))
 (hi : Nonempty (Derivation body Delta (graph4 application input domain codomain fn arg)))
 (happout : Nonempty (Derivation body Delta (graph4 application out domain codomain fnOut argOut)))
 (hof : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) fMark cutoff fn parameter)))
 (hofo : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) fMark cutoff fnOut parameter)))
 (hoa : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) aMark cutoff arg parameter)))
 (hoao : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) aMark cutoff argOut parameter)))
 (opened : Nonempty (Derivation body Delta
   (Opened p H G W out parameter cutoff mark context gamma erasedType deleted outE erasedParam keyValue rank))) :
 Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff input parameter)) := by
 let R := OriginalStructuralClassKeyDefinitions.key p H G W
 let E (i : Fin 8) : Program 8 := .composition OriginalRawSyntaxTransport.erasePackedRaw
   ![.projection 0,.projection 1,.projection i]
 let RK (i : Fin 8) : Program 8 := .composition R ![E i,.projection 7]
 let RR (i : Fin 8) : Program 8 := .composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => E i)
 let qs : Fin 13 → Program 8 := ![E 2,E 3,E 4,E 5,E 6,RK 3,RK 4,RK 5,RK 6,RR 3,RR 4,RR 5,RR 6]
 let xs : Fin 8 → OTerm alpha := ![erasedType,cutoff,input,fn,arg,fnOut,argOut,erasedParam]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 rw [graph3Rename]
 have hw := renameInto hw j Theta hj
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,graph2Rename,InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hw
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs
 have ho := renameInto ho j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ho
 have hsf := renameInto hsf j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsf
 have hsa := renameInto hsa j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsa
 have hsfo := renameInto hsfo j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsfo
 have hsao := renameInto hsao j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsao
 have harr := renameInto harr j Theta hj
 simp only [graph2Rename] at harr
 have htf := renameInto htf j Theta hj
 simp only [graph1Rename] at htf
 have htfo := renameInto htfo j Theta hj
 simp only [graph1Rename] at htfo
 have hta := renameInto hta j Theta hj
 simp only [graph1Rename] at hta
 have htao := renameInto htao j Theta hj
 simp only [graph1Rename] at htao
 have hi := renameInto hi j Theta hj
 simp only [graph4Rename] at hi
 have happout := renameInto happout j Theta hj
 simp only [graph4Rename] at happout
 have hof := renameInto hof j Theta hj
 simp only [graph3Rename] at hof
 have hofo := renameInto hofo j Theta hj
 simp only [graph3Rename] at hofo
 have hoa := renameInto hoa j Theta hj
 simp only [graph3Rename] at hoa
 have hoao := renameInto hoao j Theta hj
 simp only [graph3Rename] at hoao
 have opened := renameInto opened j Theta hj
 rw [openedRename] at opened
 let input := input.relabel j
 let out := out.relabel j
 let domain := domain.relabel j
 let codomain := codomain.relabel j
 let arrow := arrow.relabel j
 let fn := fn.relabel j
 let arg := arg.relabel j
 let fnOut := fnOut.relabel j
 let argOut := argOut.relabel j
 let parameter := parameter.relabel j
 let cutoff := cutoff.relabel j
 let fMark := fMark.relabel j
 let aMark := aMark.relabel j
 let mark := mark.relabel j
 let context := context.relabel j
 let gamma := gamma.relabel j
 let erasedType := erasedType.relabel j
 let deleted := deleted.relabel j
 let outE := outE.relabel j
 let erasedParam := erasedParam.relabel j
 let keyValue := keyValue.relabel j
 let rank := rank.relabel j
 let xx : Fin 8 → OTerm beta := ![erasedType,cutoff,input,fn,arg,fnOut,argOut,erasedParam]
 have hxs : (fun a => (xs a).relabel j) = xx := by
   funext a
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
     (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) a
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [hxs] using hq i
 have er0 := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) (.projection 1) (.projection 2)
   (ys 0) erasedType cutoff input xx (hq' 0) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 2 xx)
 have er1 := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) (.projection 1) (.projection 3)
   (ys 1) erasedType cutoff fn xx (hq' 1) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 3 xx)
 have er2 := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) (.projection 1) (.projection 4)
   (ys 2) erasedType cutoff arg xx (hq' 2) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 4 xx)
 have er3 := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) (.projection 1) (.projection 5)
   (ys 3) erasedType cutoff fnOut xx (hq' 3) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 5 xx)
 have er4 := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) (.projection 1) (.projection 6)
   (ys 4) erasedType cutoff argOut xx (hq' 4) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 6 xx)
 have kf := binaryRecover R (E 3) (.projection 7) (ys 5) (ys 1) erasedParam xx (hq' 5) (hq' 1) (projectionValue 7 xx)
 have ka := binaryRecover R (E 4) (.projection 7) (ys 6) (ys 2) erasedParam xx (hq' 6) (hq' 2) (projectionValue 7 xx)
 have kfo := binaryRecover R (E 5) (.projection 7) (ys 7) (ys 3) erasedParam xx (hq' 7) (hq' 3) (projectionValue 7 xx)
 have kao := binaryRecover R (E 6) (.projection 7) (ys 8) (ys 4) erasedParam xx (hq' 8) (hq' 4) (projectionValue 7 xx)
 have rf := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (E 3) (ys 9) (ys 1) xx (hq' 9) (hq' 1)
 have ra := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (E 4) (ys 10) (ys 2) xx (hq' 10) (hq' 2)
 have rfo := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (E 5) (ys 11) (ys 3) xx (hq' 11) (hq' 3)
 have rao := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (E 6) (ys 12) (ys 4) xx (hq' 12) (hq' 4)
 have hp := andLeft opened
 have hl := andLeft (andRight opened)
 have hd := andLeft (andRight (andRight opened))
 have hins := andLeft (andRight (andRight (andRight opened)))
 have erOut := andLeft (andRight (andRight (andRight (andRight opened))))
 have hep := andLeft (andRight (andRight (andRight (andRight (andRight opened)))))
 have sourceOutE := andLeft (andRight (andRight (andRight (andRight (andRight (andRight opened))))))
 have windowOutE := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened)))))))
 have activeOutE := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened))))))))
 have keyOutE := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened)))))))))
 have rankOutE := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened))))))))))
 have pairMark := (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight opened)))))))))))
 have window0 := windowAtPair p.window input parameter input parameter context gamma gamma hp hp hw
 have active0 := (erasedActiveAtCoordinates p H G W input parameter (ys 0) erasedParam erasedType cutoff context gamma deleted hp hep hins er0 hs window0).2.2
 have window1 := windowAtPair p.window input parameter fn parameter context gamma gamma hp hp hw
 have active1 := (erasedActiveAtCoordinates p H G W fn parameter (ys 1) erasedParam erasedType cutoff context gamma deleted hp hep hins er1 hsf window1).2.2
 have window2 := windowAtPair p.window input parameter arg parameter context gamma gamma hp hp hw
 have active2 := (erasedActiveAtCoordinates p H G W arg parameter (ys 2) erasedParam erasedType cutoff context gamma deleted hp hep hins er2 hsa window2).2.2
 have window3 := windowAtPair p.window input parameter fnOut parameter context gamma gamma hp hp hw
 have active3 := (erasedActiveAtCoordinates p H G W fnOut parameter (ys 3) erasedParam erasedType cutoff context gamma deleted hp hep hins er3 hsfo window3).2.2
 have window4 := windowAtPair p.window input parameter argOut parameter context gamma gamma hp hp hw
 have active4 := (erasedActiveAtCoordinates p H G W argOut parameter (ys 4) erasedParam erasedType cutoff context gamma deleted hp hep hins er4 hsao window4).2.2
 have tf := OriginalPackedApplicationErasureProof.eraseTypeCopy fn (ys 1) arrow erasedType cutoff htf er1
 have ta := OriginalPackedApplicationErasureProof.eraseTypeCopy arg (ys 2) domain erasedType cutoff hta er2
 have tfo := OriginalPackedApplicationErasureProof.eraseTypeCopy fnOut (ys 3) arrow erasedType cutoff htfo er3
 have tao := OriginalPackedApplicationErasureProof.eraseTypeCopy argOut (ys 4) domain erasedType cutoff htao er4
 have appI := OriginalPackedApplicationErasureProof.applicationErasure input domain codomain fn arg
   (ys 0) (ys 1) (ys 2) erasedType cutoff hi er0 er1 er2
 have appO := OriginalPackedApplicationErasureProof.applicationErasure out domain codomain fnOut argOut
   outE (ys 3) (ys 4) erasedType cutoff happout erOut er3 er4
 have fieldsI := OriginalLambdaTraversalApplicationFieldsProof.fromRaw arrow domain codomain (ys 1) (ys 2) (ys 0) harr tf ta appI
 have fieldsO := OriginalLambdaTraversalApplicationFieldsProof.fromRaw arrow domain codomain (ys 3) (ys 4) outE harr tfo tao appO
 have pf := positionForward R cutoff fn parameter context gamma erasedType deleted (ys 1) erasedParam (ys 5) (ys 9) fMark hp hl hd er1 hep kf rf hof
 have pa := positionForward R cutoff arg parameter context gamma erasedType deleted (ys 2) erasedParam (ys 6) (ys 10) aMark hp hl hd er2 hep ka ra hoa
 have pfo := positionForward R cutoff fnOut parameter context gamma erasedType deleted (ys 3) erasedParam (ys 7) (ys 11) fMark hp hl hd er3 hep kfo rfo hofo
 have pao := positionForward R cutoff argOut parameter context gamma erasedType deleted (ys 4) erasedParam (ys 8) (ys 12) aMark hp hl hd er4 hep kao rao hoao
 have sameF := sharedPairValues R fMark (ys 5) (ys 9) (ys 7) (ys 11) (ys 3) erasedParam pf pfo kfo rfo
 have sameA := sharedPairValues R aMark (ys 6) (ys 10) (ys 8) (ys 12) (ys 4) erasedParam pa pao kao rao
 have result := applicationAtErased p H G W (ys 0) outE domain codomain (ys 1) (ys 2) (ys 3) (ys 4)
   (ys 5) (ys 6) (ys 9) (ys 10) keyValue rank erasedParam
   active0 activeOutE active1 active3 active2 active4 fieldsI fieldsO appI appO
   kf sameF.1 ka sameA.1 rf sameF.2 ra sameA.2 keyOutE rankOutE
 exact positionBackward R cutoff input parameter context gamma erasedType deleted (ys 0) erasedParam
   keyValue rank mark hp hl hd er0 hep result.1 result.2 pairMark

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationOpenedProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationOpenedProof
