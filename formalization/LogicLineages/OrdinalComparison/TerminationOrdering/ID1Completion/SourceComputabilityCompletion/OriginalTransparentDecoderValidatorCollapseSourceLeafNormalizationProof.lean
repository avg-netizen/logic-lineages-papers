module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafTargetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentDecoderValidatorCollapse OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseSourceLeafProof
open OriginalTransparentDecoderValidatorCollapseSourceLeafTargetProof
open OriginalTransparentDecoderValidatorCollapseNormalizedProof
open OriginalTransparentLambdaFinalLogicProof (iffCompose)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem sourceLeafEquality (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base)
        (transparent p H G W).base.oldSource raw parameter)) :=
  iffCompose (opaqueAcceptance (normalizedData (refined p H G W).base) raw parameter h2 h1)
    (normalizedCoupledAt p H G W raw parameter)

theorem targetLeafEquality (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      (Acceptance (targetValidator (refined p H G W).base)
        (transparent p H G W).base.oldTarget raw parameter)) :=
  iffCompose (targetOpaqueAcceptance (normalizedData (refined p H G W).base) raw parameter h2 h1)
    (normalizedTargetAt p H G W raw parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
