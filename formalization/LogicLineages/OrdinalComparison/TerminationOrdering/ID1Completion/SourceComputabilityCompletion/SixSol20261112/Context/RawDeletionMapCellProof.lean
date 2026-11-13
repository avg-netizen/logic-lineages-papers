module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.RawDeletionMapCellProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open DeletionMapDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right InternalListCodec.consCode OriginalRawSyntaxTransport.erasePackedRaw

theorem scalarAtPairs (Q : Program 2) (rawJob typ erased childParameter packed value : OTerm alpha)
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob erased childParameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ erased)))
    (hv : Nonempty (Derivation body Delta (graph2 (rawScalarFromJob Q) value rawJob typ))) :
    Nonempty (Derivation body Delta (graph2 Q value packed childParameter)) := by
  let xs : Fin 2 → OTerm alpha := ![rawJob,typ]
  have rawValue := unaryValue InternalUnpair.left (.projection 0) erased rawJob xs
    (pairLeft rawJob erased childParameter hj) (projectionValue 0 xs)
  have parameterValue := unaryValue InternalUnpair.right (.projection 0) childParameter rawJob xs
    (pairRight rawJob erased childParameter hj) (projectionValue 0 xs)
  have packedValue := binaryValue InternalPairing.pairing (.projection 1) (leftOf (.projection 0))
    packed typ erased xs hp (projectionValue 1 xs) rawValue
  exact binaryRecover Q (pairOf (.projection 1) (leftOf (.projection 0))) (rightOf (.projection 0))
    value packed childParameter xs hv packedValue parameterValue

theorem atCoordinates (Q : Program 2)
    (input fake typ raw parameter cutoff rawJob value window gamma erasedType deleted erased childParameter erasedFake erasedReal : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
    (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter window deleted)))
    (hfake : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedFake z erased)))
    (hreal : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedReal typ erased)))
    (ho : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation OriginalHereditaryExpansion.unpackJob) rawJob cutoff fake parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (rawScalarFromJob Q) value rawJob typ))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter)) := by
  have fakeErase := OriginalRawSyntaxTransportInternalPackedProof.erasePackedBackward
    fake erasedFake z raw erased erasedType cutoff hf he hfake
  have fakeSelectors := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro
    cutoff fake parameter window gamma erasedType deleted erasedFake childParameter hp hl hd fakeErase hcp
  have unpacked := binaryRecover OriginalHereditaryExpansion.unpackJob
    OriginalClassContextAllPositionObserver.erasedPacked OriginalClassContextAllPositionObserver.erasedParameter
    rawJob erasedFake childParameter ![cutoff,fake,parameter] ho fakeSelectors.1 fakeSelectors.2
  have erasedValue := unaryValue InternalUnpair.right (.projection 0) erased erasedFake
    ![erasedFake,childParameter] (pairRight erasedFake z erased hfake) (projectionValue 0 ![erasedFake,childParameter])
  have rawPair := binaryRecover InternalPairing.pairing (rightOf (.projection 0)) (.projection 1)
    rawJob erased childParameter ![erasedFake,childParameter] unpacked erasedValue
    (projectionValue 1 ![erasedFake,childParameter])
  have scalar := scalarAtPairs Q rawJob typ erased childParameter erasedReal value rawPair hreal hv
  have realErase := OriginalRawSyntaxTransportInternalPackedProof.erasePackedBackward
    input erasedReal typ raw erased erasedType cutoff hi he hreal
  have realSelectors := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro
    cutoff input parameter window gamma erasedType deleted erasedReal childParameter hp hl hd realErase hcp
  exact binaryValue Q OriginalClassContextAllPositionObserver.erasedPacked
    OriginalClassContextAllPositionObserver.erasedParameter value erasedReal childParameter
    ![cutoff,input,parameter] scalar realSelectors.1 realSelectors.2

/-- Total cell compiler at every arithmetic cutoff, including out of range.
Only the fake outer zero is discarded; the real original type is restored. -/
theorem rawCell (Q : Program 2) (input fake typ raw parameter cutoff rawJob value : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fake z raw)))
    (ho : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation OriginalHereditaryExpansion.unpackJob) rawJob cutoff fake parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (rawScalarFromJob Q) value rawJob typ))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter)) := by
  let window : Program 4 := leftOf (.projection 1)
  let gamma : Program 4 := rightOf (.projection 1)
  let erasedType : Program 4 := .composition InternalRawListRecursion.lookup ![.projection 2,gamma]
  let deleted : Program 4 := .composition OriginalClassContextAllPositionObserver.deleteAt ![.projection 2,gamma]
  let erased : Program 4 := .composition OriginalRawSyntaxTransport.eraseRaw ![erasedType,.projection 2,.projection 0]
  let childParameter : Program 4 := pairOf window deleted
  let erasedFake : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 0) erased
  let erasedReal : Program 4 := pairOf (.projection 3) erased
  let qs : Fin 8 → Program 4 := ![window,gamma,erasedType,deleted,erased,childParameter,erasedFake,erasedReal]
  let xs : Fin 4 → OTerm alpha := ![raw,parameter,cutoff,typ]
  apply queryCases qs xs _
  intro beta j ys Theta hTheta hq
  simp only [graph3Rename]
  let xx : Fin 4 → OTerm beta := ![raw.relabel j,parameter.relabel j,cutoff.relabel j,typ.relabel j]
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro i
          refine Fin.cases ?_ (fun k => Fin.elim0 k) i
          rfl
  rw [hxs] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph window (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph gamma (ys 1) xx)) := hq 1
  have q2 : Nonempty (Derivation body Theta (programGraph erasedType (ys 2) xx)) := hq 2
  have q3 : Nonempty (Derivation body Theta (programGraph deleted (ys 3) xx)) := hq 3
  have q4 : Nonempty (Derivation body Theta (programGraph erased (ys 4) xx)) := hq 4
  have q5 : Nonempty (Derivation body Theta (programGraph childParameter (ys 5) xx)) := hq 5
  have q6 : Nonempty (Derivation body Theta (programGraph erasedFake (ys 6) xx)) := hq 6
  have q7 : Nonempty (Derivation body Theta (programGraph erasedReal (ys 7) xx)) := hq 7
  have hi := renameInto hi j Theta hTheta
  have hf := renameInto hf j Theta hTheta
  have ho := renameInto ho j Theta hTheta
  have hv := renameInto hv j Theta hTheta
  simp only [graph2Rename,graph3Rename,zRelabel] at hi hf ho hv
  have hw := unaryRecover InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) xx q0 (projectionValue 1 xx)
  have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) xx q1 (projectionValue 1 xx)
  have hp := reconstructPair (parameter.relabel j) (ys 0) (ys 1) hw hg
  have hl := binaryRecover InternalRawListRecursion.lookup (.projection 2) gamma
    (ys 2) (cutoff.relabel j) (ys 1) xx q2 (projectionValue 2 xx) q1
  have hd := binaryRecover OriginalClassContextAllPositionObserver.deleteAt (.projection 2) gamma
    (ys 3) (cutoff.relabel j) (ys 1) xx q3 (projectionValue 2 xx) q1
  have he := ternaryRecover OriginalRawSyntaxTransport.eraseRaw erasedType (.projection 2) (.projection 0)
    (ys 4) (ys 2) (cutoff.relabel j) (raw.relabel j) xx q4 q2 (projectionValue 2 xx) (projectionValue 0 xx)
  have hcp := binaryRecover InternalPairing.pairing window deleted
    (ys 5) (ys 0) (ys 3) xx q5 q0 q3
  have hfake := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) erased
    (ys 6) z (ys 4) xx q6 (constantValue 0 xx) q4
  have hreal := binaryRecover InternalPairing.pairing (.projection 3) erased
    (ys 7) (typ.relabel j) (ys 4) xx q7 (projectionValue 3 xx) q4
  exact atCoordinates Q (input.relabel j) (fake.relabel j) (typ.relabel j) (raw.relabel j)
    (parameter.relabel j) (cutoff.relabel j) (rawJob.relabel j) (value.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7)
    hi hf hp hl hd he hcp hfake hreal ho hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.RawDeletionMapCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.RawDeletionMapCellProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.RawDeletionMapCellProof.rawCell
