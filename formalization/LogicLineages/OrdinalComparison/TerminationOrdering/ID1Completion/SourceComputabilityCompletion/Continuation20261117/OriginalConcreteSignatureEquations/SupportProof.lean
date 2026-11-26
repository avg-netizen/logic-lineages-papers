module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem successValue (n : Nat) (arity : Fin n → Nat) (raw result args packed : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadResult.headResult result raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arguments n arity) args raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed result args)))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (signature n arity) (suc packed) raw)) := by
  have hpair := binaryValue InternalPairing.pairing Continuation20261114.OriginalHeadResult.headResult (arguments n arity)
    packed result args ![raw] hp hr ha
  have hout := unaryValue .succ (pairOf Continuation20261114.OriginalHeadResult.headResult (arguments n arity))
    (suc packed) packed ![raw] (successorValue (Fin.cons packed Fin.elim0)) hpair
  exact successorBranchIntro _ _ _ (suc packed) z ![raw] hg hout

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.SupportProof
