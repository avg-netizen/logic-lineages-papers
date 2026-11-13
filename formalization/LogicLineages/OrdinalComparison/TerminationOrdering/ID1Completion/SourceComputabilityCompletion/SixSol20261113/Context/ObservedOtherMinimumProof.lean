module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMinimumProof
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
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 let D := OriginalRankGuardedLeaf.priorData (OriginalClassContextAllPositionSelection.inputs
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P) H G W
 Nonempty (Derivation body Delta (transitionGraph D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D) minimum input parameter)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let m := OriginalClassContextAllPositionSelection.inputs q H G W P
 have hhit := OriginalAllPositionMinimumSupportProof.minimumHit q H G W P input minimum parameter hd hm
 have hminDomain := OriginalAllPositionAcceptedProof.actualHitDomain q H G W P body alpha Delta input minimum parameter hd hhit
 have hminCondition := ObservedOtherPipelineProof.conditionFromDomain q H G W P minimum parameter hminDomain
 have hv := andRight (OriginalRankGuardedLeafTupleProof.conditionFactors m H G W minimum parameter hminCondition)
 have hbound := andLeft (OriginalAllPositionMinimumSupportProof.minimumFacts q H G W P input minimum parameter input hd hm)
 exact ObservedOtherTransitionProof.transitionCandidate _ _ minimum input typ parameter
   (ObservedOtherPriorProof.priorValue p H G W P input minimum parameter hd hm) hbound hv ht
   (ObservedOtherTypeProof.acceptedType p H G W P input minimum typ parameter hd hhit ht)

/-- Actual prior bounded leaf reaches the genuine minimum: numerical bound,
original validity/type, minimum idempotence and literal successor fuel are all paid. -/
theorem priorLeafAtType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input minimum typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P).base.oldRepresentative minimum input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta (graph2
   (InternalParameterizedCanonicalResultFold.leaf (OriginalRankGuardedLeaf.priorData
     (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P) H G W))
   minimum input parameter)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let m := OriginalClassContextAllPositionSelection.inputs q H G W P
 let D := OriginalRankGuardedLeaf.priorData m H G W
 let V := InternalOriginalUniformDescentSelection.validity D
 have hhit := OriginalAllPositionMinimumSupportProof.minimumHit q H G W P input minimum parameter hd hm
 have hminDomain := OriginalAllPositionAcceptedProof.actualHitDomain q H G W P body alpha Delta input minimum parameter hd hhit
 have hminType := ObservedOtherTypeProof.acceptedType p H G W P input minimum typ parameter hd hhit ht
 obtain ⟨hid⟩ := OriginalAllPositionMinimumStatementChecks.actualMinimumIdempotence q H G W P body alpha Delta input minimum parameter
 obtain ⟨hargs⟩ := andIntro hd hm
 have hfixed := Nonempty.intro (Derivation.implicationElimination hid hargs)
 have hs := priorStep p H G W P input minimum typ parameter hd hm ht
 have hf := priorStep p H G W P minimum minimum typ parameter hminDomain hfixed hminType
 have hn := ObservedOtherRepeatProof.normalizerValue D.oldRepresentative V input minimum parameter hs hf
 have hv := andRight (OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (ObservedOtherPipelineProof.conditionFromDomain q H G W P input parameter hd))
 let xs := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact successorBranchIntro (InternalApplicationValidityStack.exactOne V) D.oldRepresentative
   (normalizer D.oldRepresentative V) minimum z xs
   (sameAccept V (InternalLessThan.constantOne 2) (suc z) xs hv (InternalLessThanSupportProof.oneConstantValue xs)) hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMinimumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMinimumProof
