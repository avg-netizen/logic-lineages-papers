module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentDecoderValidatorCollapse
open OriginalTransparentDecoderValidatorCollapseProof

theorem actualFinalPutValidity : PutValidity.ActualFinalPutValidity := by
  intro p H G W body alpha Delta s t parameter typ raw head base label
  dsimp only
  let D := selected p H G W
  let A := graph2 (InternalOriginalUniformDescentSelection.validity D) (numeral 1) s parameter ⊓
    (graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base ⊓
        graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he := actualOriginalTransparentDecoderFinalSourceCollapse p H G W
  have ha := iffForward (he body alpha (A :: Delta) (numeral 1) s parameter) (andLeft h)
  have moved := PutValidityPackedProof.packed H G
    (InternalOriginalUniformContextMembership.contextMember p.base.member) W
    s t parameter typ raw head base label ha (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  obtain ⟨out⟩ := iffBackward (he body alpha (A :: Delta) (numeral 1) t parameter) moved
  exact ⟨Derivation.implicationIntroduction out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityProof
