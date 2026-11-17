module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.RetainedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.PoolProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.PoolProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261116
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSupportProof (symm)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem accepted (n : Nat) (arity : Fin n → Nat) (H G : Program 1)
    (seed param pool candidate : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed param)))
    (hp : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target H G)
      (OriginalCandidates.candidates n arity H)) pool seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool candidate))) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) candidate param)) := by
  have h := OriginalCandidateInstallation.PoolProof.forward n arity H G seed param pool candidate ht hp hm
  apply OriginalTypedDecoderInternalBranchProof.orCases h
  · have he : Nonempty (Derivation body (eqn candidate seed :: Delta) (eqn seed candidate)) :=
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
    exact headTransport (OriginalTypedDecoder.target H G) (numeral 1) seed candidate ![param] he (withHyp ht _)
  · have hc : Nonempty (Derivation body
        ((OriginalClassCodes.Targets.meaning n arity H seed param candidate ⊓
          OriginalCandidates.Targets.retained H seed param candidate) :: Delta)
        (OriginalClassCodes.Targets.meaning n arity H seed param candidate ⊓
          OriginalCandidates.Targets.retained H seed param candidate)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact RetainedProof.accepted H G seed param candidate (withHyp ht _) (andRight hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.PoolProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.PoolProof
