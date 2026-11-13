module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.GraphCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.EndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAcceptanceSupportProof
open UniformCertificateCompletion
open GraphCongruenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both wrapper layers, the neutral guard's full zero/nonzero computation,
and the hereditary ORIGINAL-path recursion are transported compositionally.
The recursion lemma retains the same actual beta sequence and every step.
Thus rejecting guards are preserved as well as accepted guards. -/
theorem closedLeafCongruence (endpoint other : Program 6)
    (oldStep : Program 4) (window : Program 1)
    (he : ProgramGraphEquivalent endpoint other) :
    ProgramGraphEquivalent
      (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window oldStep)
      (OriginalHereditaryLambdaGlobal.closedLeaf other window oldStep) := by
  repeat' first
    | exact he
    | exact equivalentRefl _
    | apply compositionCongruence
    | apply recursionCongruence
    | intro i; fin_cases i

theorem actualClosedEndpointTransport : ActualClosedEndpointTransport := by
  intro p H G W oldStep window
  apply closedLeafCongruence _ _ oldStep window
  intro body alpha Delta out xs
  have hx : ![xs 0,xs 1,xs 2,xs 3,xs 4,xs 5] = xs := by
    funext i
    fin_cases i <;> rfl
  rw [← hx]
  exact EndpointProof.actualFinalEndpoint p H G W body alpha Delta out
    (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5)

/-- Arbitrary original inputs, including arbitrary initial representatives,
share the same final effective-leaf correspondence. This has no calibration
or separately supplied transport premise. -/
theorem finalChecker (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    ProgramGraphEquivalent
      (OriginalLambdaTraversalSelection.finalInputs
        (OriginalTransparentDecoderValidatorCollapse.refined p H G W)).oldStep
      (OriginalHereditaryLambdaGlobal.closedLeaf
        (OriginalMixedLiteralEndpointDefinitions.endpoint H G
          (InternalOriginalUniformContextMembership.contextMember p.base.member) W)
        p.window p.oldStep) := by
  rw [ClosedSelectionProof.actualFinalClosedLeafIdentity]
  exact actualClosedEndpointTransport p H G W p.oldStep p.window

theorem actualPreparedKernelClosedChecker : ActualPreparedKernelClosedChecker := by
  intro p H G W P
  let q := OriginalMixedPrepared.prepared p H G W
  let K := OriginalActiveClassKernel.classTest q H G W P
  let Q := OriginalActiveObservedClass.classTest q H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  let seed := OriginalTransparentMinimum.minimumInputs H G Q q
  exact finalChecker (OriginalRankGuardedRepresentative.guardedInputs H G W seed) H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedTransportProof
