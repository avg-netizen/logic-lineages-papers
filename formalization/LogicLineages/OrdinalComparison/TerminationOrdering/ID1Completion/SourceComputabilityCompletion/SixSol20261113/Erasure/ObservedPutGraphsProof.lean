module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasurePackingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutGraphsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalFinalVariableCanonicalSupportProof (iffForward iffBackward)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

abbrev finalData (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) :=
  ObservedPut.finalData p H G W P
abbrev finalLeaf (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) :=
  (ObservedPut.finalInputs p H G W P).oldStep
abbrev member (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs) :=
  InternalOriginalUniformContextMembership.contextMember p.base.member
abbrev literalSource (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) :=
  OriginalTransparentMixedDirectBottom.source H G (member p) W
abbrev closedChecker (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) :=
  OriginalMixedClosedTraceDefinitions.checker H G (member p) W
    (PutIntegration.seed p H G W).oldStep p.window
abbrev literalEndpoint (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) :=
  OriginalMixedLiteralEndpointDefinitions.endpoint H G (member p) W
abbrev guarded (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) :=
  OriginalRankGuardedRepresentative.guardedInputs H G W
    (OriginalAllPositionStructuralTraversalDefinitions.minimumInputs (ObservedPut.prepared p H G W) H G W P)

theorem finalSource (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) :
    SixSol20261112.Integration.ProgramGraphEquivalent
      (InternalOriginalUniformDescentSelection.validity (finalData p H G W P)) (literalSource p H G W) := by
  intro body alpha Delta out xs
  have hx : ![xs 0,xs 1] = xs := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [← hx]
  exact OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalSourceCollapse
    (guarded p H G W P) H G W body alpha Delta out (xs 0) (xs 1)

theorem finalTarget (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) :
    SixSol20261112.Integration.ProgramGraphEquivalent
      (InternalOriginalUniformDescentSelection.targetValidity (finalData p H G W P))
      (OriginalTypedDecoder.target H G) := by
  let guarded := guarded p H G W P
  intro body alpha Delta out xs
  have hx : ![xs 0,xs 1] = xs := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [← hx]
  exact OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalTargetCollapse
    guarded H G W body alpha Delta out (xs 0) (xs 1)

theorem finalEndpoint (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (out d e s t a parameter : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((InternalParameterizedApplicationStepChecker.endpointGraph
        (InternalParameterizedStructuralEndpointGuard.selectedEndpoint (finalData p H G W P))
        out d e s t a parameter).iff
      (InternalParameterizedApplicationStepChecker.endpointGraph (literalEndpoint p H G W)
        out d e s t a parameter))) := by
  let guarded := guarded p H G W P
  exact SixSol20261112.Integration.EndpointProof.actualFinalEndpoint guarded H G W body alpha Delta out d e s t a parameter

theorem sourceToFinal (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (s parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P)) (numeral 1) s parameter)) :=
  iffBackward (finalSource p H G W P body alpha Delta (numeral 1)
    (Fin.cons s (Fin.cons parameter Fin.elim0))) h

theorem sourceToFinalTarget (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (s parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.targetValidity (finalData p H G W P)) (numeral 1) s parameter)) :=
  iffBackward (finalTarget p H G W P body alpha Delta (numeral 1)
    (Fin.cons s (Fin.cons parameter Fin.elim0)))
    (OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget H G (member p) W s parameter h)

theorem leafToFinal (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (s t cert parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph4 (closedChecker p H G W) (numeral 1) s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (finalLeaf p H G W P) (numeral 1) s t cert parameter)) :=
  iffBackward (SixSol20261112.Integration.ClosedTransportProof.finalChecker (guarded p H G W P) H G W
    body alpha Delta (numeral 1)
    (Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0))))) h

/-- Every original W guard is constructed from actual raw validity/type
graphs. No graph is supplied by calibration or by a target-success premise. -/
theorem guardedOfCore (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (tag s t cert parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) t parameter)))
    (hss : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag s)))
    (htt : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag t)))
    (hc : Nonempty (Derivation body Delta
      (graph4 (InternalOriginalUniformApplicationStepSelection.selectedChecker (finalData p H G W P)
        (finalLeaf p H G W P)) (numeral 1) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (UniformCertificateCompletion.stepAccepted (finalData p H G W P) (finalLeaf p H G W P)
        s t cert parameter)) := by
  exact InternalOriginalUniformStepGuardSupportProof.taggedStepAccept (finalData p H G W P)
    (finalLeaf p H G W P) tag s t cert parameter hss
    (andIntro (sourceToFinal p H G W P s parameter hs)
      (andIntro (sourceToFinal p H G W P t parameter ht)
        (andIntro (sourceToFinalTarget p H G W P t parameter ht) (andIntro htt hc))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutGraphsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutGraphsProof
