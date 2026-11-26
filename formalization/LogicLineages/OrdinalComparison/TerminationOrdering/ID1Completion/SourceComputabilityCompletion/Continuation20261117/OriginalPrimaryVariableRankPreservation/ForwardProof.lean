module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ForwardProof
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
theorem eliminate (E : Program 3) (pool ref parameter x y : OrdinaryArithmetic.Term alpha)
 (hc : Nonempty (Derivation body Delta (forwardClosedAt R E pool ref parameter)))
 (hx : Nonempty (Derivation body Delta (accepted R ref x)))
 (he : Nonempty (Derivation body Delta (graph3 E (numeral 1) x y parameter))) :
 Nonempty (Derivation body Delta (accepted R ref y)) := by
 obtain ⟨h⟩ := elimination body alpha 2 Delta _ (fun i => emb (![x,y] i)) hc
 rw [backwardWitness] at h
 obtain ⟨ha⟩ := andIntro hx he
 exact ⟨Derivation.implicationElimination h ha⟩

theorem introduce (R : Program 1) (E : Program 3) (ref parameter : OrdinaryArithmetic.Term alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (x y : OrdinaryArithmetic.Term beta),
  (∀ p ∈ Delta, p.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph1 R (ref.relabel j) x)) →
  Nonempty (Derivation body Theta (graph3 E (numeral 1) x y (parameter.relabel j))) →
  Nonempty (Derivation body Theta (graph1 R (ref.relabel j) y))) :
 Nonempty (Derivation body Delta (forwardClosed R E ref parameter)) := by
 apply introduction body alpha 2 Delta
 let x : OrdinaryArithmetic.Term (alpha ⊕ Fin 2) := .var (.inr 0)
 let y : OrdinaryArithmetic.Term (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := graph1 R (ref.relabel Sum.inl) x ⊓ graph3 E (numeral 1) x y (parameter.relabel Sum.inl)
 have ha : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := next (alpha ⊕ Fin 2) Sum.inl (A :: Delta.map (fun p => p.relabel Sum.inl)) x y
  (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)) (andLeft ha) (andRight ha)
 exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ForwardProof
