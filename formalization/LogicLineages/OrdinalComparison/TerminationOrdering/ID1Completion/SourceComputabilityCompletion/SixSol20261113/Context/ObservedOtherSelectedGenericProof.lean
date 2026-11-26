module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedGenericProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedBoundedDescentNormalizer
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem selectedStep (raw : InternalOriginalUniformDescentSelection.Data) (window : Program 1)
 (input minimum parameter : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (InternalOriginalUniformDescentSelection.validity
   (OriginalApplicationSidecar.originalData raw window)) (suc z) input parameter)))
 (hleaf : Nonempty (Derivation body Delta (graph2 (InternalParameterizedCanonicalResultFold.leaf
   (OriginalApplicationSidecar.originalData raw window)) minimum input parameter)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 let D := OriginalApplicationSidecar.selectedData raw window
 Nonempty (Derivation body Delta (transitionGraph D.oldRepresentative
   (InternalOriginalUniformDescentSelection.validity D) minimum input parameter)) := by
 let D := OriginalApplicationSidecar.selectedData raw window
 let T := transition D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D)
 apply programCases T (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta output hj hg
 have hl' := renameInto hleaf j Theta hj
 have hw' := renameInto hw j Theta hj
 have hv' := renameInto hv j Theta hj
 have ho' := renameInto hother j Theta hj
 rw [graph2Rename] at hl'
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
 simp only [graph2Rename,sucRelabel,zRelabel] at hv'
 simp only [graph1Rename,sucRelabel,zRelabel] at ho'
 simp only [consTermRename,emptyRename] at hg
 rw [InternalParameterizedBoundedDescentNormalizerSyntaxProof.transitionRename]
 change Nonempty (Derivation body Theta (graph2 T (minimum.relabel j) (input.relabel j) (parameter.relabel j)))
 have hout := OriginalRankGuardedLeafOtherStepProof.transitionPriorLeaf raw window
   output (input.relabel j) (parameter.relabel j) hw' hv' ho' hg
 have he := valueUnique (InternalParameterizedCanonicalResultFold.leaf (OriginalApplicationSidecar.originalData raw window))
   output (minimum.relabel j) (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hout hl'
 exact outputTransport T output (minimum.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedGenericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedGenericProof
