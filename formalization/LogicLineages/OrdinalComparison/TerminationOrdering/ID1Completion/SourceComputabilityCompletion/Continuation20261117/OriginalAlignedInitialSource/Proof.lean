module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalTransparentLambdaFinalLogicProof (iffSelf andIff iffCompose)
open InternalApplicationStepPeelSupportProof (andLeft)

theorem sourceField (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs) :
    (installedInputs n arity p).base.oldSource =
      OriginalUniverseDecoder.source (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n)
        (InternalOriginalUniformContextMembership.contextMember
          (OriginalContextMemberLift.liftMember (OriginalUniverseDomainCoverage.member n)))
        (OriginalGuardedHeadSourceCoverage.window n arity) := rfl

theorem alignedSource : Targets.InternalAlignedSource := by
  intro n arity p body alpha Delta input parameter typ raw context gamma hp hc
  rw [sourceField]
  have hs := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceEquation
    (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)
    (InternalOriginalUniformContextMembership.contextMember
      (OriginalContextMemberLift.liftMember (OriginalUniverseDomainCoverage.member n)))
    (OriginalGuardedHeadSourceCoverage.window n arity) input parameter typ raw context gamma hp hc
  have ha := andLeft (OriginalConcreteUniverseMemberAlignment.Proof.concreteMemberAlignment
    n arity body alpha Delta typ raw gamma context)
  exact iffCompose hs (andIff (iffSelf _) ha)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Proof
