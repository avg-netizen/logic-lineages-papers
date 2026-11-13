module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalCanonicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem finalPremises (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta
   (OriginalFunctionNeutrality.windowGraph (finalInputs p H G W P).window input parameter ⊓
    InternalParameterizedCanonicalResultFold.sourcePremises (finalData p H G W P) input typ parameter)) := by
 let m := minimumInputs p H G W P
 let r := refined p H G W P
 have hc := OriginalRankGuardedLeafTupleProof.conditionFactors m H G W input parameter
   (EvaluatorKeyOtherDomainProof.conditionFromDomain p H G W P input parameter hd)
 have hv : Nonempty (Derivation body Delta (graph2
   (InternalOriginalUniformDescentSelection.validity (OriginalLambdaTraversalSelection.leafData r.base r.window))
   (suc z) input parameter)) := by
   change Nonempty (Derivation body Delta (graph2
     (InternalOriginalUniformDescentSelection.validity (OriginalRankGuardedLeafProof.selectedData m H G W)) (suc z) input parameter))
   rw [OriginalRankGuardedLeafProof.selectedValidity]
   exact andRight hc
 change Nonempty (Derivation body Delta
   (OriginalFunctionNeutrality.windowGraph (OriginalLambdaTraversalSelection.finalInputs r).window input parameter ⊓
    InternalParameterizedCanonicalResultFold.sourcePremises (OriginalLambdaTraversalSelection.finalData r) input typ parameter))
 rw [OriginalLambdaTraversalSelectionFieldProof.finalWindow,
   OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData,
   OriginalCanonicalFoldFusionFinalProof.selectedSourcePremises]
 exact andIntro (andLeft hc) (andIntro hv ht)
theorem atType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (out input typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta
   ((graph2 (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) out input parameter).iff
    (graph2 (OriginalLambdaTraversalSelection.canonical (refined p H G W P).base (refined p H G W P).window) out input parameter))) := by
 obtain ⟨law⟩ := OriginalLambdaTraversalFinalCanonicalProof.actualOriginalLambdaTraversalFinalCanonical
   (refined p H G W P) body alpha Delta out input typ parameter
 obtain ⟨hp⟩ := finalPremises p H G W P input typ parameter hd ht
 exact ⟨Derivation.implicationElimination law hp⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldBridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldBridgeProof
