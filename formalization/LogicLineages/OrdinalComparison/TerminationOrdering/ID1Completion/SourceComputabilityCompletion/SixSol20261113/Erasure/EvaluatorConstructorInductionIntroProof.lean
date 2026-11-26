module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionInstancesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionIntroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorConstructorInductionDefinitions EvaluatorErasureDefinitions
open InternalApplicationStepPeelSupportProof (andIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualIntro (R : Program 2) (H G : Program 1) (M W : Program 2) (count : OTerm alpha)
 (applicationStep : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (xs : Fin 16 → OTerm beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (applicationFields R H G M W (count.relabel j) xs)) →
   Nonempty (Derivation body Theta (AdmittedPair R H G M W (xs 0) (xs 1) (xs 13))))
 (lambdaStep : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (xs : Fin 11 → OTerm beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (lambdaFields R H G M W (count.relabel j) xs)) →
   Nonempty (Derivation body Theta (AdmittedPair R H G M W (xs 0) (xs 1) (xs 6))))
 : Nonempty (Derivation body Delta (AtLength R H G M W count)) := by
 apply andIntro
 · apply InternalClosedProgramsBindingProof.introduction body alpha 16 Delta
   let xs : Fin 16 → OTerm (alpha ⊕ Fin 16) := fun i => .var (.inr i)
   let phi := applicationFields R H G M W (count.relabel Sum.inl) xs
   let Theta := phi :: Delta.map (fun q => q.relabel Sum.inl)
   have hf : Nonempty (Derivation body Theta phi) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have h := applicationStep (alpha ⊕ Fin 16) Sum.inl Theta xs
     (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)) hf
   exact ⟨Derivation.implicationIntroduction (Classical.choice h)⟩
 · apply InternalClosedProgramsBindingProof.introduction body alpha 11 Delta
   let xs : Fin 11 → OTerm (alpha ⊕ Fin 11) := fun i => .var (.inr i)
   let phi := lambdaFields R H G M W (count.relabel Sum.inl) xs
   let Theta := phi :: Delta.map (fun q => q.relabel Sum.inl)
   have hf : Nonempty (Derivation body Theta phi) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have h := lambdaStep (alpha ⊕ Fin 11) Sum.inl Theta xs
     (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)) hf
   exact ⟨Derivation.implicationIntroduction (Classical.choice h)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionIntroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionIntroProof
