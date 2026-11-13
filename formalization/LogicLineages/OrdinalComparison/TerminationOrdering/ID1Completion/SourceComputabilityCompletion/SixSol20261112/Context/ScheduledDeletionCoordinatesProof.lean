module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open OriginalInternalJobDeletionLookupProof (bumpRename)
open SourceComputabilityFormulaSupportProof (numeral)
open ScheduledDeletionDefinitions ScheduledDeletionSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right InternalListCodec.consCode OriginalHereditaryAnnotatedExpansion.annotation
  OriginalRawSyntaxTransport.erasePackedRaw

/-- Every output packet is queried internally after the original deletion
lookup has exposed its genuine runtime coordinates. -/
theorem atErasure (Q : Program 2) (arity : Nat)
    (input typ raw parameter cutoff rawCell annotated value window gamma erasedType deleted erased childParameter : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
    (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter window deleted)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell erased childParameter)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
    (hdecor : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate annotated (bump arity cutoff) (numeral 0) typ raw rawCell)))
    (hv : Nonempty (Derivation body Delta (graph1 (scalarFromJob Q) value annotated))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter)) := by
  let ann : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 0) (.projection 0)
  let typed : Program 3 := pairOf (.projection 0) (.projection 1)
  let packed : Program 3 := pairOf (.projection 0) (.projection 2)
  let qs : Fin 3 → Program 3 := ![ann,typed,packed]
  let xs : Fin 3 → OTerm alpha := Fin.cons typ (Fin.cons rawCell (Fin.cons erased Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph3Rename]
  let xx : Fin 3 → OTerm beta :=
    Fin.cons (typ.relabel j) (Fin.cons (rawCell.relabel j) (Fin.cons (erased.relabel j) Fin.elim0))
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ (fun k => Fin.elim0 k) i
        rfl
  rw [hxs] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph ann (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph typed (ys 1) xx)) := hq 1
  have q2 : Nonempty (Derivation body Theta (programGraph packed (ys 2) xx)) := hq 2
  have hi := renameInto hi j Theta hj
  have hp := renameInto hp j Theta hj
  have hl := renameInto hl j Theta hj
  have hd := renameInto hd j Theta hj
  have he := renameInto he j Theta hj
  have hcp := renameInto hcp j Theta hj
  have hc := renameInto hc j Theta hj
  have ha := renameInto ha j Theta hj
  have hdecor := renameInto hdecor j Theta hj
  have hv := renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,bumpRename,
    GuardedSourceSyntaxProof.numeralRename] at hi hp hl hd he hcp hc ha hdecor hv
  have annPair := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 0) (.projection 0)
    (ys 0) (numeral 0) (typ.relabel j) xx q0 (constantValue 0 xx) (projectionValue 0 xx)
  have typedPair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 1) (typ.relabel j) (rawCell.relabel j) xx q1 (projectionValue 0 xx) (projectionValue 1 xx)
  have packedPair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 2)
    (ys 2) (typ.relabel j) (erased.relabel j) xx q2 (projectionValue 0 xx) (projectionValue 2 xx)
  have notBelow := OriginalInternalAnnotationOffsetProof.notBelowBump (body := body) (Delta := Theta) arity (cutoff.relabel j)
  have annotation := OriginalInternalAnnotationInheritedProof.actualInherited body beta Theta
    (bump arity (cutoff.relabel j)) (numeral 0) (typ.relabel j) (raw.relabel j)
    (numeral arity) (ys 0) ha notBelow annPair
  have annotatedPair := decoratedPair (bump arity (cutoff.relabel j)) (numeral 0)
    (typ.relabel j) (raw.relabel j) (rawCell.relabel j) (annotated.relabel j) (ys 0) (ys 1)
    annotation annPair typedPair hdecor
  have scalar := scalarAtPairs Q (annotated.relabel j) (numeral 0) (ys 1)
    (typ.relabel j) (rawCell.relabel j) (erased.relabel j) (childParameter.relabel j)
    (ys 2) (value.relabel j) annotatedPair typedPair hc packedPair hv
  have packedErase := OriginalRawSyntaxTransportInternalPackedProof.erasePackedBackward
    (input.relabel j) (ys 2) (typ.relabel j) (raw.relabel j) (erased.relabel j)
    (erasedType.relabel j) (cutoff.relabel j) hi he packedPair
  have selectors := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro
    (cutoff.relabel j) (input.relabel j) (parameter.relabel j) (window.relabel j)
    (gamma.relabel j) (erasedType.relabel j) (deleted.relabel j) (ys 2) (childParameter.relabel j)
    hp hl hd packedErase hcp
  exact binaryValue Q OriginalClassContextAllPositionObserver.erasedPacked
    OriginalClassContextAllPositionObserver.erasedParameter (value.relabel j)
    (ys 2) (childParameter.relabel j)
    ![cutoff.relabel j,input.relabel j,parameter.relabel j] scalar selectors.1 selectors.2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionCoordinatesProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionCoordinatesProof.atErasure
