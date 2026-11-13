module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem actualPreparedKernelStepObjectCertificate : ActualPreparedKernelStepObjectCertificate := by
  intro p H G W P body alpha Delta context
    parameter gamma source typ raw target step x y quotient entry path first second
  let f := preparedKernelFinalInputs p H G W P
  let D := preparedKernelFinalData p H G W P
  let A := StepObjectCertificateFields p H G W P context
    parameter gamma source typ raw target step x y quotient entry path first second
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hwindow := andLeft (andLeft h)
  have hparameter := andRight (andLeft h)
  have hsource := andLeft (andLeft (andRight h))
  have hw := andRight (andLeft (andRight h))
  have hx := andLeft (andLeft (andRight (andRight h)))
  have hy := andRight (andLeft (andRight (andRight h)))
  have hcodes := andLeft (andRight (andRight (andRight h)))
  have hedge := andLeft hcodes
  have hentry := andLeft (andRight hcodes)
  have hpath := andRight (andRight hcodes)
  have hobjects := andRight (andRight (andRight (andRight h)))
  have hfirst := andLeft hobjects
  have hsecond := andRight hobjects
  have he : Nonempty (Derivation body (A :: Delta)
      (edgeAccepted D f.oldStep x y quotient parameter)) :=
    InternalParameterizedQuotientEdgeCheckerNormalizedProof.normalizedAcceptEncoded
      D f.oldStep x y quotient source target step parameter hedge
      (andIntro hw (andIntro hx hy))
  have htypes := OriginalPositiveCertificateFieldsProof.typedOutputs p H G W P
    source typ raw target step x y parameter (numeral context) gamma hsource hparameter hw hx hy
  have htx : Nonempty (Derivation body (A :: Delta) (typedAccepted D x typ parameter)) := by
    simpa only [typedAccepted,InternalOriginalUniformDescentSelection.typedAccepted,
      InternalOriginalUniformDescentSelection.selectedTyped,numeral,InternalOriginalStepGuard.one]
      using andLeft htypes
  have hty : Nonempty (Derivation body (A :: Delta) (typedAccepted D y typ parameter)) := by
    simpa only [typedAccepted,InternalOriginalUniformDescentSelection.typedAccepted,
      InternalOriginalUniformDescentSelection.selectedTyped,numeral,InternalOriginalStepGuard.one]
      using andRight htypes
  have hg := OriginalPositiveCertificateSpineProof.quotientSpine p H G W P context
    x y quotient parameter gamma hwindow hparameter he
  have hzero : Nonempty (Derivation body (A :: Delta)
      (graph2 InternalListCodec.consCode path entry z)) := by
    simpa only [numeral] using hpath
  have hpositive := OriginalFunctionChildCertificateGuardProof.singletonPositive D f.oldStep
    x y quotient entry path parameter he hentry hzero
  have hraw := OriginalFunctionChildCertificateGuardProof.positiveFromGuard
    (edgeChecker D f.oldStep) x y quotient path parameter hg hpositive
  have hwindowOne : Nonempty (Derivation body (A :: Delta)
      (graph1 f.window InternalOriginalStepGuard.one (numeral context))) := by
    simpa only [numeral,InternalOriginalStepGuard.one] using hwindow
  obtain ⟨hcertificate⟩ := OuterPositiveProof.positiveAccept f.oldSrc f.oldComp D
    (RawScalar.checker D) f.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    f.window context typ first second path gamma x y parameter hwindowOne
    (pairLeft first gamma x hfirst) (pairLeft second gamma y hsecond)
    (pairRight first gamma x hfirst) (pairRight second gamma y hsecond)
    hparameter htx hty hraw
  exact ⟨Derivation.implicationIntroduction hcertificate⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateProof
