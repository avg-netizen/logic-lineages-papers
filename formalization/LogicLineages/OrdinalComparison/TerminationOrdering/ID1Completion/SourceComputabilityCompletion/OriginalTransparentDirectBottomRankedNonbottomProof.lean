module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedNonbottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (suc z)
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open UniformCertificateCompletion
open OriginalHereditaryLambdaGlobal

theorem rawNonbottom (source : Program 2) (oldStep : Program 4) (s t cert parameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (h : Nonempty (Derivation body Delta (graph4 (OriginalTransparentDirectBottom.refined source oldStep) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hcert := unaryValue OriginalTransparentDirectBottom.certificateCode (.projection 0) cert s xs hc (projectionValue 0 xs)
 have hactive := InternalApplicationStepPeelSupportProof.sameAccept (.projection 2) (.composition OriginalTransparentDirectBottom.certificateCode (fun _ : Fin 1 => .projection 0)) cert xs (projectionValue 2 xs) hcert
 have hb := successorBranchElim OriginalTransparentDirectBottom.active oldStep (OriginalTransparentDirectBottom.acceptedValue source) (suc z) z xs hactive h
 have hc1 := conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs hb
 have hc2 := conjunctionRecover (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom) xs (andRight hc1)
 exact PositiveSpineRulesSupportProof.nonBottomRecover BottomRepresentative.bottomTest xs (andLeft hc2)

theorem finalNonbottom (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (s t cert parameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (h : Nonempty (Derivation body Delta (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not) :=
 rawNonbottom (OriginalTransparentDirectBottomGlobal.source p H G W) p.oldStep s t cert parameter hc
  (OriginalTransparentDirectBottomFreshZeroLeafProof.initialAcceptance p H G W P s t cert parameter hc h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedNonbottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedNonbottomProof
