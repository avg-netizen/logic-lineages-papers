module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherNormalizeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherSelectedGenericProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherSelectedProof
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
 (hd : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 let D := OriginalRankGuardedLeafProof.selectedData (EvaluatorKeyPut.minimumInputs p H G W P) H G W
 Nonempty (Derivation body Delta (transitionGraph D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D) minimum input parameter)) := by
 let m := EvaluatorKeyPut.minimumInputs p H G W P
 let raw := OriginalRankGuardedLeafTupleProof.rawData m H G W
 let window := (OriginalRankGuardedLeaf.refined m H G W).window
 let D := OriginalRankGuardedLeafProof.selectedData m H G W
 let T := transition D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D)
 have hleaf := EvaluatorKeyOtherNormalizeProof.priorLeafAtType p H G W P input minimum typ parameter hd hm ht hother
 have hf := OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (EvaluatorKeyOtherDomainProof.conditionFromDomain p H G W P input parameter hd)
 exact ObservedOtherSelectedGenericProof.selectedStep raw window input minimum parameter
   (andLeft hf) (andRight hf) hleaf hother

theorem selectedLeafAtType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input minimum typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalLambdaTraversalSelection.leaf
     (EvaluatorKeyPut.refined p H G W P).base
     (EvaluatorKeyPut.refined p H G W P).window) minimum input parameter)) := by
 let m := EvaluatorKeyPut.minimumInputs p H G W P
 let raw := OriginalRankGuardedLeafTupleProof.rawData m H G W
 let window := (OriginalRankGuardedLeaf.refined m H G W).window
 let D := OriginalRankGuardedLeafProof.selectedData m H G W
 let V := InternalOriginalUniformDescentSelection.validity D
 have hhit := EvaluatorKeyOtherMinimumProof.minimumHit p H G W P input minimum parameter hd hm
 have hdmin := andLeft hhit
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W input minimum parameter hd hdmin (andRight hhit)
 have htmin := SixSol20261113.Erasure.EvaluatorOtherMarksTypeTransferProof.actualTypeTransfer (EvaluatorKeyPut.baseRepresentative p H G W) H G (EvaluatorKeyPut.member p H G W) W input minimum parameter typ had ht
 have hfixed := EvaluatorKeyOtherMinimumProof.idempotent p H G W P input minimum parameter hd hm
 have hc := OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (EvaluatorKeyOtherDomainProof.conditionFromDomain p H G W P input parameter hd)
 have hprior := EvaluatorKeyOtherNormalizeProof.priorLeafAtType p H G W P input minimum typ parameter hd hm ht hother
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherSelectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherSelectedProof
