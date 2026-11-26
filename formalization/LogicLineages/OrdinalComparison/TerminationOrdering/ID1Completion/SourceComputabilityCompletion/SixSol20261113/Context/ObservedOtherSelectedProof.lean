module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedGenericProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem selectedStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input minimum typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 let D := OriginalRankGuardedLeafProof.selectedData (OriginalClassContextAllPositionSelection.inputs
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P) H G W
 Nonempty (Derivation body Delta (transitionGraph D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D) minimum input parameter)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let m := OriginalClassContextAllPositionSelection.inputs q H G W P
 let raw := OriginalRankGuardedLeafTupleProof.rawData m H G W
 let window := (OriginalRankGuardedLeaf.refined m H G W).window
 let D := OriginalRankGuardedLeafProof.selectedData m H G W
 let T := transition D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D)
 have hleaf := ObservedOtherMinimumProof.priorLeafAtType p H G W P input minimum typ parameter hd hm ht
 have hf := OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (ObservedOtherPipelineProof.conditionFromDomain q H G W P input parameter hd)
 exact ObservedOtherSelectedGenericProof.selectedStep raw window input minimum parameter
   (andLeft hf) (andRight hf) hleaf hother

theorem selectedLeafAtType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input minimum typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalLambdaTraversalSelection.leaf
     (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
     (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window) minimum input parameter)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let m := OriginalClassContextAllPositionSelection.inputs q H G W P
 let raw := OriginalRankGuardedLeafTupleProof.rawData m H G W
 let window := (OriginalRankGuardedLeaf.refined m H G W).window
 let D := OriginalRankGuardedLeafProof.selectedData m H G W
 let V := InternalOriginalUniformDescentSelection.validity D
 have hhit := OriginalAllPositionMinimumSupportProof.minimumHit q H G W P input minimum parameter hd hm
 have hdmin := OriginalAllPositionAcceptedProof.actualHitDomain q H G W P body alpha Delta input minimum parameter hd hhit
 have htmin := ObservedOtherTypeProof.acceptedType p H G W P input minimum typ parameter hd hhit ht
 obtain ⟨hid⟩ := OriginalAllPositionMinimumStatementChecks.actualMinimumIdempotence q H G W P body alpha Delta input minimum parameter
 obtain ⟨hargs⟩ := andIntro hd hm
 have hfixed := Nonempty.intro (Derivation.implicationElimination hid hargs)
 have hc := OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (ObservedOtherPipelineProof.conditionFromDomain q H G W P input parameter hd)
 have hprior := ObservedOtherMinimumProof.priorLeafAtType p H G W P input minimum typ parameter hd hm ht
 have homin := OriginalRankGuardedLeafOtherStepProof.priorOtherTag raw window minimum input parameter
   (andLeft hc) (andRight hc) hprior hother
 have hs := selectedStep p H G W P input minimum typ parameter hd hm ht hother
 have hf := selectedStep p H G W P minimum minimum typ parameter hdmin hfixed htmin homin
 have hn := ObservedOtherRepeatProof.normalizerValue D.oldRepresentative V input minimum parameter hs hf
 have hv : Nonempty (Derivation body Delta (graph2 V (suc z) input parameter)) := by
   change Nonempty (Derivation body Delta (graph2 (InternalOriginalUniformDescentSelection.validity
     (OriginalRankGuardedLeafProof.selectedData m H G W)) (suc z) input parameter))
   rw [OriginalRankGuardedLeafProof.selectedValidity]
   exact andRight hc
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact successorBranchIntro (InternalApplicationValidityStack.exactOne V) D.oldRepresentative
   (normalizer D.oldRepresentative V) minimum z xs
   (sameAccept V (InternalLessThan.constantOne 2) (suc z) xs hv (InternalLessThanSupportProof.oneConstantValue xs)) hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedProof
