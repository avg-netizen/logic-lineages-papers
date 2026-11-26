module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportMembershipProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectMembershipProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalUniverseDecoderInternalAcceptance OriginalUniverseDecoderInternalAcceptanceSyntaxProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof (singletonCases)
open OriginalUniverseDecoderInternalAcceptanceOutputProof (outputCases)
open OriginalUniverseDecoderInternalAcceptanceGuardRootProof (termRootForward)
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- An accepted original universe run pays its actual first request's root
membership guard. This is an internal first-step consequence of the unchanged
checker, with no constructor, native evaluation or well-formedness premise. -/
theorem termMember (H : Program 1) (M W : Program 2)
    (typ raw gamma c : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Delta (graph2 M (numeral 1) typ c)) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Theta state work request hj hs hc hr
  simp only [graph2Rename,numeralRename]
  have ha' := renameInto ha j Theta hj
  rw [termAcceptedRename] at ha'
  apply outputCases H M W 0 state work request (gamma.relabel j) (typ.relabel j)
    (raw.relabel j) (c.relabel j) _ hs hc hr ha'
  intro beta' k Xi out hk hguard _ _
  simp only [graph2Rename,numeralRename]
  have hr' := renameInto hr k Xi hk
  simp only [stepRequestRename,numeralRename] at hr'
  exact andLeft (termRootForward M W (request.relabel k)
    ((gamma.relabel j).relabel k) ((typ.relabel j).relabel k)
    ((raw.relabel j).relabel k) ((c.relabel j).relabel k) hr' hguard)

/-- SAME-final source validity supplies the actual root member at an actual
parameter pair. The all-output transparent-source bridge retains the original
universe checker; its paid root guard is transported to normalized membership. -/
theorem selectedMemberFromSource (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2)
    (packed typ parameter c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ packed)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selected p H G W))
        (numeral 1) packed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (selected p H G W).member (numeral 1) typ parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons packed Fin.elim0) _
  intro beta j Theta raw hj hr
  simp only [graph2Rename,numeralRename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Theta hj
  rw [graph2Rename] at hp'
  have ht' := renameInto ht j Theta hj
  rw [graph1Rename] at ht'
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,numeralRename] at hs'
  have hpacked := reconstructPair (packed.relabel j) (typ.relabel j) raw ht' hr
  obtain ⟨he⟩ := OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalSourceCollapse
    p H G W body beta Theta (numeral 1) (packed.relabel j) (parameter.relabel j)
  obtain ⟨hs0⟩ := hs'
  have hsource := Derivation.implicationElimination (Derivation.conjunctionLeft he) hs0
  have hfields := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsElim
    H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
    (packed.relabel j) (parameter.relabel j) (typ.relabel j) raw (c.relabel j)
    (gamma.relabel j) hpacked hp' ⟨hsource⟩
  rw [OriginalCanonicalizedTypedTransportMembershipProof.selectedMember]
  exact InternalOriginalUniformContextMembershipInternalProof.sliceAccept p.base.member
    (numeral 1) (typ.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
    hp' (termMember H (InternalOriginalUniformContextMembership.contextMember p.base.member)
      W (typ.relabel j) raw (gamma.relabel j) (c.relabel j) (andRight hfields))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectMembershipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectMembershipProof
