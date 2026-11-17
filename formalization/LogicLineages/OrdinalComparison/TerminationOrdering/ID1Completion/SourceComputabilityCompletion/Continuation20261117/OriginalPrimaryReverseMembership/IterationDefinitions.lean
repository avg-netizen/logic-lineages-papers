module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Iteration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114

/-- Quantify the actual output only; retain fixed pool, original seed, carrier and parameter. -/
def matrix {alpha : Type} (E : Program 3) (count pool reached parameter carrier seed : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 1) :=
 (graph4 (PrimaryIteration.iterate E) (.var (.inr 0)) (count.relabel Sum.inl) (pool.relabel Sum.inl)
  (reached.relabel Sum.inl) (parameter.relabel Sum.inl)).imp
 ((allAccepted (pool.relabel Sum.inl) (carrier.relabel Sum.inl) (seed.relabel Sum.inl) (reached.relabel Sum.inl)).imp
  (allAccepted (pool.relabel Sum.inl) (carrier.relabel Sum.inl) (seed.relabel Sum.inl) (.var (.inr 0))))
def AtCount {alpha : Type} (E : Program 3) (count pool reached parameter carrier seed : OrdinaryArithmetic.Term alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix E count pool reached parameter carrier seed)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Iteration
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Iteration
