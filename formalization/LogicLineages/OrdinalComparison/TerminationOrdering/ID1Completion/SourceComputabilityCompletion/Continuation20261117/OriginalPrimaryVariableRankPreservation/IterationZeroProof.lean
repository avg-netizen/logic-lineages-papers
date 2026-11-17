module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationProof
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
variable {R : Program 1}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Iteration IterationSyntaxProof SyntaxProof
theorem rowZero (E : Program 3) (pool reached parameter carrier seed : OrdinaryArithmetic.Term alpha) :
 Nonempty (Derivation body Delta (AtCount R E z pool reached parameter carrier seed)) := by
 apply introduction body alpha 1 Delta
 let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
 let A := graph4 (PrimaryIteration.iterate E) out z (pool.relabel Sum.inl) (reached.relabel Sum.inl) (parameter.relabel Sum.inl)
 let B : Formula (alpha ⊕ Fin 1) := allAcceptedAt R (pool.relabel Sum.inl) (carrier.relabel Sum.inl) (seed.relabel Sum.inl) (reached.relabel Sum.inl)
 obtain ⟨h⟩ := zeroCore (body := body) (Delta := B :: A :: Delta.map (fun p => p.relabel Sum.inl)) E
   (pool.relabel Sum.inl) (reached.relabel Sum.inl) (parameter.relabel Sum.inl) out (carrier.relabel Sum.inl) (seed.relabel Sum.inl)
   ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationProof
