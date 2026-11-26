module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutFinalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutFinalSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutFinalCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem actualFinalPutObjectCertificate : EvaluatorKeyPutTargets.ActualFinalPutObjectCertificate := by
  intro p H G W P body alpha Delta context s t cert parameter typ raw head base label
    gamma x y quotient entry path first second
  let f := finalInputs p H G W P
  let D := finalData p H G W P
  let Window := graph1 f.window (numeral 1) (numeral context) ⊓
    graph2 InternalPairing.pairing parameter (numeral context) gamma
  let Folds := InternalParameterizedCanonicalResultFold.foldGraph D x s parameter ⊓
    InternalParameterizedCanonicalResultFold.foldGraph D y t parameter
  let Codes := graph3 edgeCode quotient s t cert ⊓
    (graph2 InternalPairing.pairing entry y quotient ⊓
      graph2 InternalListCodec.consCode path entry (numeral 0))
  let Objects := graph2 InternalPairing.pairing first gamma x ⊓ graph2 InternalPairing.pairing second gamma y
  let A := Fields p H G W P s t cert parameter typ raw head base label ⊓
    (Window ⊓ (Folds ⊓ (Codes ⊓ Objects)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := andLeft h
  have hw := EvaluatorKeyPutFinalStepProof.step p H G W P s t cert parameter typ raw head base label
    (andLeft hf) (andLeft (andRight hf)) (andLeft (andRight (andRight hf)))
    (andLeft (andRight (andRight (andRight hf)))) (andRight (andRight (andRight (andRight hf))))
  have hwindow := andLeft (andLeft (andRight h))
  have hparameter := andRight (andLeft (andRight h))
  have hsource := andLeft (andRight hf)
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
      D f.oldStep x y quotient s t cert parameter hedge
      (andIntro hw (andIntro hx hy))
  have htypes := EvaluatorKeyPutFinalFieldsProof.typedOutputs p H G W P
    s typ raw t cert x y parameter (numeral context) gamma hsource hparameter hw hx hy
  have htx : Nonempty (Derivation body (A :: Delta) (typedAccepted D x typ parameter)) := by
    simpa only [typedAccepted,InternalOriginalUniformDescentSelection.typedAccepted,
      InternalOriginalUniformDescentSelection.selectedTyped,numeral,InternalOriginalStepGuard.one]
      using andLeft htypes
  have hty : Nonempty (Derivation body (A :: Delta) (typedAccepted D y typ parameter)) := by
    simpa only [typedAccepted,InternalOriginalUniformDescentSelection.typedAccepted,
      InternalOriginalUniformDescentSelection.selectedTyped,numeral,InternalOriginalStepGuard.one]
      using andRight htypes
  have hg := EvaluatorKeyPutFinalSpineProof.quotientSpine p H G W P context
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutFinalCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutFinalCertificateProof
