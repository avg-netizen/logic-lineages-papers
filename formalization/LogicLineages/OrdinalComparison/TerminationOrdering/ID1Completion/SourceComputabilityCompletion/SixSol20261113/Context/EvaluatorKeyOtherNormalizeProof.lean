module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherPriorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTypeTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherNormalizeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalParameterizedBoundedDescentNormalizer
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem priorStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input minimum typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 let D := OriginalRankGuardedLeaf.priorData (EvaluatorKeyPut.minimumInputs p H G W P) H G W
 Nonempty (Derivation body Delta (transitionGraph D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D) minimum input parameter)) := by
 let m := EvaluatorKeyPut.minimumInputs p H G W P
 have hhit := EvaluatorKeyOtherMinimumProof.minimumHit p H G W P input minimum parameter hd hm
 have hminDomain := andLeft hhit
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W input minimum parameter hd hminDomain (andRight hhit)
 have hminCondition := EvaluatorKeyOtherDomainProof.conditionFromDomain p H G W P minimum parameter hminDomain
 have hv := andRight (OriginalRankGuardedLeafTupleProof.conditionFactors m H G W minimum parameter hminCondition)
 have hbound := andLeft (EvaluatorKeyMinimumSupportProof.minimumFacts p H G W P input minimum parameter input hd hm)
 exact ObservedOtherTransitionProof.transitionCandidate _ _ minimum input typ parameter
   (EvaluatorKeyOtherPriorProof.priorValue p H G W P input minimum parameter hd hm hother) hbound hv ht
   (SixSol20261113.Erasure.EvaluatorOtherMarksTypeTransferProof.actualTypeTransfer (EvaluatorKeyPut.baseRepresentative p H G W) H G (EvaluatorKeyPut.member p H G W) W input minimum parameter typ had ht)

/-- Actual prior bounded leaf reaches the genuine minimum: numerical bound,
original validity/type, minimum idempotence and literal successor fuel are all paid. -/
theorem priorLeafAtType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input minimum typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 Nonempty (Derivation body Delta (graph2
   (InternalParameterizedCanonicalResultFold.leaf (OriginalRankGuardedLeaf.priorData
     (EvaluatorKeyPut.minimumInputs p H G W P) H G W))
   minimum input parameter)) := by
 let m := EvaluatorKeyPut.minimumInputs p H G W P
 let D := OriginalRankGuardedLeaf.priorData m H G W
 let V := InternalOriginalUniformDescentSelection.validity D
 have hhit := EvaluatorKeyOtherMinimumProof.minimumHit p H G W P input minimum parameter hd hm
 have hminDomain := andLeft hhit
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W input minimum parameter hd hminDomain (andRight hhit)
 have hminType := SixSol20261113.Erasure.EvaluatorOtherMarksTypeTransferProof.actualTypeTransfer (EvaluatorKeyPut.baseRepresentative p H G W) H G (EvaluatorKeyPut.member p H G W) W input minimum parameter typ had ht
 have hfixed := EvaluatorKeyOtherMinimumProof.idempotent p H G W P input minimum parameter hd hm
 have hotmin := EvaluatorKeyOtherTransferProof.otherTransfer (EvaluatorKeyPut.baseRepresentative p H G W) H G (EvaluatorKeyPut.member p H G W) W input minimum parameter had hother
 have hs := priorStep p H G W P input minimum typ parameter hd hm ht hother
 have hf := priorStep p H G W P minimum minimum typ parameter hminDomain hfixed hminType hotmin
 have hn := ObservedOtherRepeatProof.normalizerValue D.oldRepresentative V input minimum parameter hs hf
 have hv := andRight (OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (EvaluatorKeyOtherDomainProof.conditionFromDomain p H G W P input parameter hd))
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact successorBranchIntro (InternalApplicationValidityStack.exactOne V) D.oldRepresentative
   (normalizer D.oldRepresentative V) minimum z xs
   (sameAccept V (InternalLessThan.constantOne 2) (suc z) xs hv (InternalLessThanSupportProof.oneConstantValue xs)) hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherNormalizeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherNormalizeProof
