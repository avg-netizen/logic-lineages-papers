module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationControlProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open OriginalLambdaGuardLeaf
open OriginalHereditaryLambdaChildBranchProof (activeRename)
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof

theorem lambdaGuardReject (source : Program 2) (s t cert parameter : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s))) :
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentLambdaStep.hopGuard source) (suc z) s t cert parameter).not) := by
 let A := graph4 (OriginalTransparentLambdaStep.hopGuard source) (suc z) s t cert parameter
 have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hrest := andRight (conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs ha)
 have hs := andLeft (conjunctionRecover OriginalLambdaGuardLeaf.sourceLambda _ xs hrest)
 have htest := unaryRecover OriginalLambdaGuardLeaf.lambdaTest (.projection 0) (suc z) s xs hs (projectionValue 0 xs)
 have hone := sameRightRecover OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
  (suc z) ![s] htest (InternalLessThanSupportProof.oneConstantValue _)
 obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (suc z) (suc (suc z)) ![s] hone (withHyp ht A)
 obtain ⟨hn⟩ := (OriginalHereditaryValidityInternalBranchProof.oneNotTwo :
  Nonempty (Derivation body (A :: Delta) (equal (suc z : OTerm alpha) (suc (suc z))).not))
 exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn (by simpa only [A, equalEqn, SourceComputabilityFormulaSupportProof.numeral] using he))⟩

theorem applicationAtLive (source : Program 2) (s t cert parameter state next : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (hg : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard source) (suc z) s t cert parameter)))
 (hc : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert parameter))) :
 Nonempty (Derivation body Delta (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state)) := by
 have hguard := OriginalHereditaryLambdaChildStateProof.atLiveValue
  (OriginalTransparentApplicationFunctionDefinitions.hopGuard source) (suc z) state s t cert parameter hl hg
 have hchild := OriginalHereditaryLambdaChildStateProof.atLiveValue
  OriginalTransparentApplicationFunctionDefinitions.childLive next state s t cert parameter hl hc
 have happ : Nonempty (Derivation body Delta (graph1 (OriginalTransparentApplicationFunctionDefinitions.transition source) next state)) :=
  successorBranchIntro _ _ _ next z ![state] (normalizeAccept _ ![state] hguard) hchild
 let A := graph1 (OriginalHereditaryLambda.atState (OriginalTransparentLambdaStep.hopGuard source)) (suc z) state
 have hn : Nonempty (Derivation body Delta A.not) := by
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hget := OriginalHereditaryLambdaChildStateProof.atLiveRecover
   (OriginalTransparentLambdaStep.hopGuard source) (suc z) state s t cert parameter (withHyp hl A) ha
  obtain ⟨hno⟩ := lambdaGuardReject source s t cert parameter (withHyp ht A)
  obtain ⟨hget⟩ := hget
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hno hget)⟩
 exact zeroBranchIntro _ _ _ next ![state] (normalizeReject _ ![state] hn) happ
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationControlProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationControlProof
