module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafPriorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOtherTagTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalApplicationSidecar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- OTHER is the accepted original test, not an assumed structural equation.
It internally rejects the exact application-opening guard. -/
theorem closedGuard (guard : Program 2) (input parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z input parameter)) := by
  let T := InternalApplicationStepPeel.same OriginalLambdaTraversal.rawTag (two 1)
  let C := graph1 T (suc z) input
  have hn := OriginalFinalOtherValidityTagProof.otherNotTwo input ho
  have hc : Nonempty (Derivation body Delta C.not) := by
    have htwo := InternalStructuralEndpointGuardSupportProof.sameRightRecover
      OriginalLambdaTraversal.rawTag (two 1) (suc (suc z)) (Fin.cons input Fin.elim0)
      (show Nonempty (Derivation body (C :: Delta) C) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (twoValue (Fin.cons input Fin.elim0))
    obtain ⟨hn'⟩ := withHyp hn C
    obtain ⟨htwo⟩ := htwo
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn' htwo)⟩
  have hz := OriginalTransparentLambdaValidityInternalBooleanProof.sameReject
    OriginalLambdaTraversal.rawTag (two 1) (Fin.cons input Fin.elim0) hc
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.liftP T) z input parameter)) :=
    unaryValue T (.projection 0) z input xs hz (projectionValue 0 xs)
  exact InternalApplicationResultStackCompositionFrameConstructorsProof.conjunctionRejectLeft
    (InternalParameterizedApplicationResultStack.liftP T) guard xs hl

/-- At every active OTHER input the actual selected transition is an actual
prior-leaf output. The type selector is bound internally, not supplied by an
extra run assumption or inferred from native decoding. -/
theorem transitionPriorLeaf (data : Data) (window : Program 1)
    (out input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window))
        (suc z) input parameter)))
    (ho : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input)))
    (ht : Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph
        (selectedData data window).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (selectedData data window)) out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro beta j Theta typ hj hl
  rw [graph2Rename]
  have hw' := renameInto hw j Theta hj
  have hv' := renameInto hv j Theta hj
  have ho' := renameInto ho j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  simp only [graph1Rename,sucRelabel,zRelabel] at ho'
  rw [InternalParameterizedBoundedDescentNormalizerSyntaxProof.transitionRename] at ht'
  change Nonempty (Derivation body Theta
    (graph2 (InternalParameterizedBoundedDescentNormalizer.transition
      (selectedData data window).oldRepresentative
      (InternalOriginalUniformDescentSelection.validity (selectedData data window)))
      (out.relabel j) (input.relabel j) (parameter.relabel j))) at ht'
  simp only [consTermRename,emptyRename] at hl
  have hp := andIntro hw' (andIntro hv' hl)
  obtain ⟨hi⟩ := OriginalApplicationSidecarTransitionProof.transitionIff data window
    (out.relabel j) (input.relabel j) typ (parameter.relabel j) hp
  obtain ⟨ht'⟩ := ht'
  have hc : Nonempty (Derivation body Theta
      (graph2 (fold data window) (out.relabel j) (input.relabel j) (parameter.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) ht'⟩
  exact OriginalApplicationSidecarRootMarkLeafProof.closedLeafGraph data window
    (out.relabel j) (input.relabel j) (parameter.relabel j) hc
    (closedGuard _ (input.relabel j) (parameter.relabel j) ho')

/-- Recover the common original raw tag from the prior selected leaf's
already proved root-mark preservation. -/
theorem priorRawTag (data : Data) (window : Program 1)
    (out input parameter tag : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag tag input))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag tag out)) := by
  apply programCases OriginalConstructorShape.mark (Fin.cons input Fin.elim0) _
  intro beta j Theta mark hj hm
  rw [graph1Rename]
  have hw' := renameInto hw j Theta hj
  have hv' := renameInto hv j Theta hj
  have hl' := renameInto hl j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [graph2Rename] at hl'
  rw [graph1Rename] at ht'
  simp only [consTermRename,emptyRename] at hm
  obtain ⟨hi⟩ := OriginalApplicationSidecarRootMarkLeafProof.leafMarkIff data window
    (out.relabel j) (input.relabel j) (parameter.relabel j) mark hw' hv' hl'
  obtain ⟨hm⟩ := hm
  have hout : Nonempty (Derivation body Theta
      (graph1 OriginalConstructorShape.mark mark (out.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hm⟩
  exact OriginalConstructorShapeRootFieldsProof.sharedTag mark (input.relabel j) (out.relabel j)
    (tag.relabel j) ⟨hm⟩ hout ht'

/-- In particular OTHER remains true after that actual prior-leaf output. -/
theorem priorOtherTag (data : Data) (window : Program 1)
    (out input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) out)) := by
  apply programCases OriginalLambdaTraversal.rawTag (Fin.cons input Fin.elim0) _
  intro beta j Theta tag hj htag
  simp only [graph1Rename,sucRelabel,zRelabel]
  have hw' := renameInto hw j Theta hj
  have hv' := renameInto hv j Theta hj
  have hl' := renameInto hl j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [graph2Rename] at hl'
  simp only [graph1Rename,sucRelabel,zRelabel] at ht'
  simp only [consTermRename,emptyRename] at htag
  have hout := priorRawTag data window (out.relabel j) (input.relabel j)
    (parameter.relabel j) tag hw' hv' hl' htag
  exact OriginalLambdaTraversalOtherTagTransportProof.atSameTag
    (input.relabel j) (out.relabel j) tag (suc z) htag hout ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
