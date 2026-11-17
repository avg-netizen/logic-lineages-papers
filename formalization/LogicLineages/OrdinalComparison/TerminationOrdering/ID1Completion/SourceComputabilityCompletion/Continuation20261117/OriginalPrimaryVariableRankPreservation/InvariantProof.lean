module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.InvariantProof
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

open SyntaxProof
theorem eliminateAt (pool carrier seed reached x : OrdinaryArithmetic.Term alpha)
 (hall : Nonempty (Derivation body Delta (allAcceptedAt R pool carrier seed reached)))
 (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached x))) :
 Nonempty (Derivation body Delta (acceptedAt R pool carrier seed x)) := by
 obtain ⟨h⟩ := elimination body alpha 1 Delta _ (fun _ => emb x) hall
 rw [memberWitness] at h
 obtain ⟨hm⟩ := hm
 exact ⟨Derivation.implicationElimination h hm⟩
theorem introduce (pool carrier seed reached : OrdinaryArithmetic.Term alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (x : OrdinaryArithmetic.Term beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 contains (numeral 1) (reached.relabel j) x)) →
   Nonempty (Derivation body Theta (acceptedAt R (pool.relabel j) (carrier.relabel j) (seed.relabel j) x))) :
 Nonempty (Derivation body Delta (allAcceptedAt R pool carrier seed reached)) := by
 apply introduction body alpha 1 Delta
 let x : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
 let A := graph2 contains (numeral 1) (reached.relabel Sum.inl) x
 obtain ⟨h⟩ := next (alpha ⊕ Fin 1) Sum.inl (A :: Delta.map (fun p => p.relabel Sum.inl)) x
  (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩

theorem eliminate (R : Program 1) (ref reached x : OrdinaryArithmetic.Term alpha)
 (hall : Nonempty (Derivation body Delta (allAccepted R ref reached)))
 (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached x))) :
 Nonempty (Derivation body Delta (graph1 R ref x)) :=
 eliminateAt (R := R) ref ref ref reached x hall hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.InvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.InvariantProof
