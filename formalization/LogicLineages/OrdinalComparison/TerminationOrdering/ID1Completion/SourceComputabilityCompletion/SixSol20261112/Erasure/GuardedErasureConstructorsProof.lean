module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureFinalGraphsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.SelectedNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedCongruenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedCongruenceLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureConstructorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalFinalVariableCanonicalSupportProof (iffBackward)
open GuardedErasureTargets GuardedErasureFinalGraphsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambdaNonapplication (s : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) s))) :
    Nonempty (Derivation body Delta (OriginalNonapplicationChecker.nonapplicationRoot s)) := by
  let A := graph1 (InternalApplicationStepPeel.constructorTag (.projection 0)) positionTerm s
  have hp : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (suc z) positionTerm (Fin.cons s Fin.elim0)
    (withHyp hs A) hp
  rw [positionTermEq] at he
  obtain ⟨hn⟩ := (OriginalHereditaryValidityInternalBranchProof.oneNotTwo :
    Nonempty (Derivation body (A :: Delta) (equal (suc z : OTerm alpha) (suc (suc z))).not))
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination hn (by simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he))⟩

/-- A literal nil certificate is introduced into the ACTUAL final selected
checker, after internally transporting the concrete retained C leaf. -/
theorem atNil (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (tag s t cert parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) t parameter)))
    (hss : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag s)))
    (htt : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag t)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)))
    (hc : Nonempty (Derivation body Delta (graph4 (closedChecker p H G W) (numeral 1) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (Certificate (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W) s t cert parameter)) := by
  have hf := leafToFinal p H G W P s t cert parameter hc
  have hcore := SelectedNilProof.backward
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint (finalData p H G W P))
    (finalLeaf p H G W P) (numeral 1) s t cert parameter hp hf
  exact andIntro hc (guardedOfCore p H G W P tag s t cert parameter hs ht hss htt hcore)

/-- Lambda/nonapplication roots retain the actual original scanner at this
same certificate; no child scanner invariant is assumed. -/
theorem atNonapplication (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (tag s t cert parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) t parameter)))
    (hss : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag s)))
    (htt : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag t)))
    (hn : Nonempty (Derivation body Delta (OriginalNonapplicationChecker.nonapplicationRoot s)))
    (hc : Nonempty (Derivation body Delta (graph4 (closedChecker p H G W) (numeral 1) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (Certificate (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W) s t cert parameter)) := by
  have hf := leafToFinal p H G W P s t cert parameter hc
  have hcore := OriginalNonapplicationCheckerCollapseProof.checkerBackward
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint (finalData p H G W P))
    (finalLeaf p H G W P) (numeral 1) s t cert parameter hn hf
  exact andIntro hc (guardedOfCore p H G W P tag s t cert parameter hs ht hss htt hcore)

/-- The actual parent certificate is supplied once by stepLift. Both C and
the full original W are constructed at that SAME lifted certificate. -/
theorem applicationAtCertificate (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (s t parameter childS childT arg d e arrow cert childCert : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (OriginalMixedExistentialCongruenceDefinitions.ApplicationFrame (literalSource p H G W)
        s t parameter childS childT arg d e arrow)))
    (hend : Nonempty (Derivation body Delta
      (InternalParameterizedApplicationStepChecker.endpointGraph (literalEndpoint p H G W)
        (numeral 1) d e childS childT arg parameter)))
    (hp : Nonempty (Derivation body Delta (graph1 stepLift cert childCert)))
    (hc : Nonempty (Derivation body Delta
      (Certificate (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)
        childS childT childCert parameter))) :
    Nonempty (Derivation body Delta
      (Certificate (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)
        s t cert parameter)) := by
  have hh := OriginalMixedClosedCongruenceApplicationProof.frameHop (literalSource p H G W)
    s t parameter childS childT arg d e arrow cert childCert hf hp
  have hclosed := OriginalApplicationWrapperEndpointOnlyProof.actualEndpointIntroduction
    (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
    (literalEndpoint p H G W) p.window
    (OriginalMixedClosedPrefixProof.applicationRaw (literalSource p H G W)
      (OriginalTransparentDirectBottom.refined (literalSource p H G W) p.oldStep))
    body alpha Delta s t cert parameter childS childT childCert arg d e arrow hh hend (andLeft hc)
  have h1 := andRight hf
  have h2 := andRight h1
  have h3 := andRight h2
  have hendpoint := iffBackward (finalEndpoint p H G W P (numeral 1) d e childS childT arg parameter) hend
  have hlift : Nonempty (Derivation body Delta
      (InternalOriginalUniformStepGuard.liftPremises (finalData p H G W P)
        arrow d e childS childT arg childCert s t cert parameter)) :=
    andIntro (andIntro (andLeft h3) (andIntro hendpoint (andIntro (andLeft h1) (andLeft h2)))) hp
  have hw := InternalOriginalUniformStepGuardApplicationProof.applicationStep
    (finalData p H G W P) (finalLeaf p H G W P)
    arrow d e childS childT arg childCert s t cert parameter hlift (andRight hc)
  exact andIntro hclosed hw

/-- The existing lambda prefix constructs C at the parent. Both raw lambda
types and the genuine context-extension frame pay the original W guards. -/
theorem lambdaAtCertificate (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (s t parameter childS childT childParam d e context gamma extended arrow cert childCert : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (OriginalLambdaErasureSquareDichotomyDefinitions.Frame (literalSource p H G W)
        s t parameter childS childT childParam d e context gamma extended)))
    (ht : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) t parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow arrow d e)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryLambda.prefixCertificate cert childCert)))
    (hc : Nonempty (Derivation body Delta
      (Certificate (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)
        childS childT childCert childParam))) :
    Nonempty (Derivation body Delta
      (Certificate (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)
        s t cert parameter)) := by
  have hh := OriginalLambdaErasureSquareDichotomyProof.frameHop (literalSource p H G W)
    s t parameter childS childT childParam d e context gamma extended cert childCert hf hp
  obtain ⟨law⟩ := OriginalMixedClosedPrefixProof.actualLambda (literalSource p H G W)
    (OriginalTransparentDirectBottom.refined (literalSource p H G W) p.oldStep)
    (literalEndpoint p H G W) p.window body alpha Delta s t cert parameter
    childS childT childCert childParam d e context gamma extended
  obtain ⟨prem⟩ := andIntro hh (andLeft hc)
  have hclosed : Nonempty (Derivation body Delta
      (graph4 (closedChecker p H G W) (numeral 1) s t cert parameter)) :=
    ⟨Derivation.implicationElimination law prem⟩
  have h1 := andRight hf
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  have hsf := OriginalLambdaConstructorGraphFieldsProof.constructorFields s d e childS arrow
    (andLeft h1) (andLeft h3) ha
  have htf := OriginalLambdaConstructorGraphFieldsProof.constructorFields t d e childT arrow
    (andLeft h2) (andLeft h4) ha
  exact atNonapplication p H G W P arrow s t cert parameter (andLeft hf) ht
    (andLeft (andRight hsf)) (andLeft (andRight htf)) (lambdaNonapplication s (andLeft hsf)) hclosed
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureConstructorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureConstructorsProof
