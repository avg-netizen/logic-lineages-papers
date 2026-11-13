module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.FinalErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.EndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceMemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof (projectionValue)
open OriginalFinalVariableCanonicalSupportProof (iffForward)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem finalMember (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    (preparedKernelFinalData p H G W P).member =
      OriginalMixedLiteralEndpointDefinitions.memberAt
        (InternalOriginalUniformContextMembership.contextMember p.base.member) := by
  let q := OriginalMixedPrepared.prepared p H G W
  let K := OriginalActiveClassKernel.classTest q H G W P
  let Q := OriginalActiveObservedClass.classTest q H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  let seed := OriginalTransparentMinimum.minimumInputs H G Q q
  exact EndpointProof.selectedMember
    (OriginalRankGuardedRepresentative.guardedInputs H G W seed) H G W

theorem memberValue (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (typ parameter c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hm : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformContextMembership.contextMember p.base.member)
        (numeral 1) typ c))) :
    Nonempty (Derivation body Delta
      (graph2 (preparedKernelFinalData p H G W P).member (numeral 1) typ parameter)) := by
  rw [finalMember]
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  let xs : Fin 2 → OTerm alpha := (Fin.cons typ (Fin.cons parameter Fin.elim0))
  exact binaryValue M (.projection 0) (leftOf (.projection 1)) (numeral 1) typ c xs hm
    (projectionValue 0 xs)
    (unaryValue InternalUnpair.left (.projection 1) c parameter xs
      (pairLeft parameter c gamma hp) (projectionValue 1 xs))

/-- The real source decoder supplies the actual type membership. Both
canonical endpoints are then typed by the existing internally proved fold
theorem, at the same type and parameter. No typing premise is added. -/
theorem typedOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3)
    (source typ raw target step x y parameter c gamma : OTerm alpha)
    (hsource : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing source typ raw)))
    (hparameter : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hw : Nonempty (Derivation body Delta
      (stepAccepted (preparedKernelFinalData p H G W P)
        (preparedKernelFinalInputs p H G W P).oldStep source target step parameter)))
    (hx : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph
        (preparedKernelFinalData p H G W P) x source parameter)))
    (hy : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph
        (preparedKernelFinalData p H G W P) y target parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (InternalOriginalUniformDescentSelection.selectedTyped
          (preparedKernelFinalData p H G W P)) (numeral 1) x typ parameter ⊓
        graph3 (InternalOriginalUniformDescentSelection.selectedTyped
          (preparedKernelFinalData p H G W P)) (numeral 1) y typ parameter)) := by
  let f := preparedKernelFinalInputs p H G W P
  let D := preparedKernelFinalData p H G W P
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  have hs := pairLeft source typ raw hsource
  have hparts := InternalOriginalUniformStepGuardSupportProof.taggedStepRecover
    D f.oldStep typ source target step parameter hs hw
  have hvs := andLeft hparts
  have hvt := andLeft (andRight hparts)
  have hlt := andLeft (andRight (andRight (andRight hparts)))
  have hliteral : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) source parameter)) := by
    simpa only [graph2,OriginalTransparentMixedDirectBottom.source,M,
      numeral,InternalOriginalStepGuard.one] using
      (iffForward (FinalErasureProof.finalSource p H G W P body alpha Delta
        InternalOriginalStepGuard.one (Fin.cons source (Fin.cons parameter Fin.elim0))) hvs)
  have fields := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsElim
    H G M W source parameter typ raw c gamma hsource hparameter hliteral
  have hm := OriginalInternalBottomSourceMemberProof.termMembership H M W
    typ raw gamma c (andRight fields)
  have hmFinal := memberValue p H G W P typ parameter c gamma hparameter hm
  have hvsOne : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity D) (numeral 1) source parameter)) := by
    simpa only [numeral,InternalOriginalStepGuard.one] using hvs
  have hvtOne : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity D) (numeral 1) target parameter)) := by
    simpa only [numeral,InternalOriginalStepGuard.one] using hvt
  exact andIntro
    (OriginalCanonicalizedTypedTransportFoldProof.foldTyped D x source typ parameter
      hvsOne hs hmFinal hx)
    (OriginalCanonicalizedTypedTransportFoldProof.foldTyped D y target typ parameter
      hvtOne hlt hmFinal hy)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateFieldsProof
