module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open OriginalTransparentDecoderValidatorCollapse OriginalTransparentDecoderValidatorCollapseTargets
open OriginalTransparentDecoderValidatorCollapseSourceInductionProof
open OriginalTransparentDecoderValidatorCollapseOutputProof
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The all-raw acceptance collapse is promoted to every output of the two
actual Boolean Programs, including exact rejection on all malformed inputs. -/
theorem actualOriginalTransparentDecoderSourceCollapse : ActualOriginalTransparentDecoderSourceCollapse := by
  intro p H G W body alpha Gamma out raw parameter
  let N := normalizedData (refined p H G W).base
  exact validatorConjunctionOutput (sourceRoot N) (targetRoot N) N.member
    (.composition G ![leftOf (.projection 1)])
    (.composition (OriginalUniverseDecoder.termCheck H
      (InternalOriginalUniformContextMembership.contextMember p.base.member) W)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1),leftOf (.projection 1)])
    out raw parameter (sourceAcceptance p H G W raw parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceProof
