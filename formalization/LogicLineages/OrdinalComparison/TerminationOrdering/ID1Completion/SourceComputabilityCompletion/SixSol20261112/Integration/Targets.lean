module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All outputs of the original selected endpoint, at its SAME actual final
Data, agree internally with the literal decoder endpoint. Every six input
coordinates, including the actual runtime parameter, are retained. -/
def EndpointLaw (data : InternalOriginalUniformDescentSelection.Data)
    (H G : Program 1) (M W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out d e s t a parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((InternalParameterizedApplicationStepChecker.endpointGraph
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
      out d e s t a parameter).iff
     (InternalParameterizedApplicationStepChecker.endpointGraph
      (OriginalMixedLiteralEndpointDefinitions.endpoint H G M W)
      out d e s t a parameter)))

def ActualFinalEndpoint : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    EndpointLaw (OriginalTransparentDecoderValidatorCollapse.selected p H G W)
      H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W

/-- The checked literal trace now reconstructs the endpoint at the actual
selected final Data. The child recognizer is the unchanged original restricted
recognizer; no final-leaf or unrestricted-source equivalence is asserted. -/
def ActualFinalApplicationEndpoint : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter fn targetFn childCert arg d e arrow fp ap : OTerm alpha),
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  Nonempty (Derivation body Delta
    (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg s)) →
  Nonempty (Derivation body Delta
    (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop
      (OriginalUniverseDecoder.source H G M W)
      s t cert parameter fn targetFn childCert arg d e arrow)) →
  Nonempty (Derivation body Delta (graph4
    (OriginalMixedDirectBottomTrace.recognizes (OriginalUniverseDecoder.source H G M W)
      (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep))
    (numeral 1) fn targetFn childCert parameter)) →
  Nonempty (Derivation body Delta
    (InternalParameterizedApplicationStepChecker.endpointGraph
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint
        (OriginalTransparentDecoderValidatorCollapse.selected p H G W))
      (numeral 1) d e fn targetFn arg parameter))

/-- The very minimum and final pipeline named by the retained checked
active-kernel package; this is an alias for that original Data. -/
def kernelFinalData (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : InternalOriginalUniformDescentSelection.Data :=
  let K := OriginalActiveClassKernel.classTest p H G W P
  let Q := OriginalActiveObservedClass.classTest p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  let s := OriginalTransparentMinimum.minimumInputs H G Q p
  OriginalLambdaTraversalSelection.finalData (OriginalFinalGuardedRank.refined s H G W)

/-- Keep the entire previous active-kernel package and append the independent
endpoint identification at its identical final Data. No second tuple is chosen. -/
def ActualKernelFinalRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalActiveKernelMinimum.Properties n arity p H G W P ∧
    EndpointLaw (kernelFinalData p H G W P) H G
      (InternalOriginalUniformContextMembership.contextMember p.base.member) W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
