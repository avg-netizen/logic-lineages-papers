module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open OriginalPositionStructuralKeyOpeningDefinitions OriginalPositionStructuralKeyOpeningSupportProof
open OriginalPositionStructuralKeyObserverWiringProof
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Proof-side coordinate assembly. Every transformed coordinate is an actual
graph supplied by the opening/erasure geometry stage, not a new premise of
ActualLambda. Activation is derived from original source and Insert. -/
theorem atCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out d e child childOut parameter childParameter cutoff childMark mark context gamma deleted childGamma childDeleted erasedType inputE outE childE childOutE erasedParam erasedChildParam childKey otherKey childRank otherRank keyValue rank : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)))
 (hsc : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) child childParameter)))
 (hsco : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) childOut childParameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter context childGamma)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam context deleted)))
 (hecp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedChildParam context childDeleted)))
 (hcons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma d gamma)))
 (hecons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted d deleted)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (hin : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)))
 (hcin : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType (suc cutoff) childDeleted childGamma)))
 (hei : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw inputE erasedType cutoff input)))
 (heo : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw outE erasedType cutoff out)))
 (hec : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childE erasedType (suc cutoff) child)))
 (heco : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childOutE erasedType (suc cutoff) childOut)))
 (hfi : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields inputE d e childE erasedParam erasedChildParam)))
 (hfo : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields outE d e childOutE erasedParam erasedChildParam)))
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor inputE d e childE)))
 (hout : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor outE d e childOutE)))
 (hkc : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) childKey childE erasedChildParam)))
 (hkco : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) otherKey childOutE erasedChildParam)))
 (hrc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw childRank childE)))
 (hrco : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw otherRank childOutE)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank outE)))
 (hk : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) keyValue outE erasedParam)))
 (hoc : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) childMark (suc cutoff) child childParameter)))
 (hoco : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) childMark (suc cutoff) childOut childParameter)))
 (hmark : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark keyValue rank)))
 :
 Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff input parameter)) := by
 let K := OriginalStructuralClassKeyDefinitions.key p H G W
 have shifted := OriginalPositionStructuralKeyLambdaContextProof.shiftedLookupAndDeletion
   gamma deleted childGamma childDeleted d cutoff erasedType hcons hecons hl hd
 have wchild := windowAtPair p.window input parameter child childParameter context gamma childGamma hp hcp hw
 have wother := windowAtPair p.window input parameter childOut childParameter context gamma childGamma hp hcp hw
 have wo := windowAtPair p.window input parameter out parameter context gamma gamma hp hp hw
 have ai := (erasedActiveAtCoordinates p H G W input parameter inputE erasedParam erasedType cutoff context gamma deleted hp hep hin hei hs hw).2.2
 have ao := (erasedActiveAtCoordinates p H G W out parameter outE erasedParam erasedType cutoff context gamma deleted hp hep hin heo ho wo).2.2
 have ac := (erasedActiveAtCoordinates p H G W child childParameter childE erasedChildParam erasedType (suc cutoff) context childGamma childDeleted hcp hecp hcin hec hsc wchild).2.2
 have aco := (erasedActiveAtCoordinates p H G W childOut childParameter childOutE erasedChildParam erasedType (suc cutoff) context childGamma childDeleted hcp hecp hcin heco hsco wother).2.2
 have first := positionForward K (suc cutoff) child childParameter context childGamma erasedType childDeleted childE erasedChildParam childKey childRank childMark hcp shifted.1 shifted.2 hec hecp hkc hrc hoc
 have second := positionForward K (suc cutoff) childOut childParameter context childGamma erasedType childDeleted childOutE erasedChildParam otherKey otherRank childMark hcp shifted.1 shifted.2 heco hecp hkco hrco hoco
 have shared := OriginalPositionStructuralKeyApplicationCoreProof.sharedPairValues K childMark childKey childRank otherKey otherRank childOutE erasedChildParam first second hkco hrco
 have parent := OriginalPositionStructuralKeyLambdaCoreProof.lambdaAtErased p H G W
   inputE outE d e childE childOutE childKey childRank keyValue rank erasedParam erasedChildParam
   ai ao ac aco hfi hfo hi hout hkc shared.1 hrc shared.2 hk hr
 exact positionBackward K cutoff input parameter context gamma erasedType deleted inputE erasedParam keyValue rank mark hp hl hd hei hep parent.1 parent.2 hmark

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoordinatesProof
