module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.IterationStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.IterationProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Iteration IterationSyntaxProof SyntaxProof
theorem rowSuccessor (E : Program 3) (count pool reached parameter carrier seed : OrdinaryArithmetic.Term alpha)
 (hback : Nonempty (Derivation body Delta (backClosed E pool carrier parameter)))
 (hrow : Nonempty (Derivation body Delta (AtCount E count pool reached parameter carrier seed))) :
 Nonempty (Derivation body Delta (AtCount E (suc count) pool reached parameter carrier seed)) := by
 apply introduction body alpha 1 Delta
 let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
 let D := Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 have hj : ∀ p ∈ Delta, p.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ D := by
  intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩
 let A := graph4 (PrimaryIteration.iterate E) out (suc (count.relabel Sum.inl)) (pool.relabel Sum.inl) (reached.relabel Sum.inl) (parameter.relabel Sum.inl)
 let B : Formula (alpha ⊕ Fin 1) := allAccepted (pool.relabel Sum.inl) (carrier.relabel Sum.inl) (seed.relabel Sum.inl) (reached.relabel Sum.inl)
 have hback' := renameInto hback Sum.inl D hj
 rw [backClosedRename] at hback'
 have hrow' := renameInto hrow Sum.inl D hj
 rw [atCountRename] at hrow'
 obtain ⟨h⟩ := successorCore E (count.relabel Sum.inl) (pool.relabel Sum.inl) (reached.relabel Sum.inl)
   (parameter.relabel Sum.inl) out (carrier.relabel Sum.inl) (seed.relabel Sum.inl)
   (withHyp (withHyp hback' A) B) (withHyp (withHyp hrow' A) B)
   ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.IterationProof
