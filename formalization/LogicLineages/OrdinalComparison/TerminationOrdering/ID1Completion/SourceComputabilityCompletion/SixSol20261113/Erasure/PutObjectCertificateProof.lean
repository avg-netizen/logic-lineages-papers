module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutFinalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutObjectCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors UniformCertificateCompletion PutIntegration
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)

theorem actualFinalPutObjectCertificate : ActualFinalPutObjectCertificate := by
  intro p H G W P body alpha Delta context s t cert parameter typ raw head base label
    gamma x y quotient entry path first second
  let Window := graph1 (finalInputs p H G W P).window (numeral 1) (numeral context) ⊓
    graph2 InternalPairing.pairing parameter (numeral context) gamma
  let Folds := InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) x s parameter ⊓
    InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) y t parameter
  let Codes := graph3 edgeCode quotient s t cert ⊓
    (graph2 InternalPairing.pairing entry y quotient ⊓
      graph2 InternalListCodec.consCode path entry (numeral 0))
  let Objects := graph2 InternalPairing.pairing first gamma x ⊓ graph2 InternalPairing.pairing second gamma y
  let A := Fields p H G W P s t cert parameter typ raw head base label ⊓
    (Window ⊓ (Folds ⊓ (Codes ⊓ Objects)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := andLeft h
  have hw := PutFinalStepProof.step p H G W P s t cert parameter typ raw head base label
    (andLeft hf) (andLeft (andRight hf)) (andLeft (andRight (andRight hf)))
    (andLeft (andRight (andRight (andRight hf)))) (andRight (andRight (andRight (andRight hf))))
  have input := andIntro (andLeft (andRight h))
    (andIntro (andIntro (andLeft (andRight hf)) hw) (andRight (andRight h)))
  obtain ⟨law⟩ := SixSol20261112.Integration.OriginalPositiveCertificateProof.actualPreparedKernelStepObjectCertificate
    (seed p H G W) H G W P body alpha (A :: Delta) context
    parameter gamma s typ raw t cert x y quotient entry path first second
  obtain ⟨input⟩ := input
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination law input)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutObjectCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutObjectCertificateProof
