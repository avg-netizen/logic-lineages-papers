module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalBetaTotalityProof InternalQuotientComparisonProof
open Iteration IterationSyntaxProof SyntaxProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (count seed parameter pool reached out boundsRef rootTypeRef : OrdinaryArithmetic.Term alpha)
    (had : Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta
      (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n))
        (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hi : Nonempty (Derivation body Delta
      (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity)) out count pool reached parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (allAccepted n arity out rootTypeRef boundsRef)) :=
  rowApply n arity count pool reached parameter out boundsRef rootTypeRef
    (allCounts n arity count seed parameter pool reached boundsRef rootTypeRef had hpool) hi hu
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
