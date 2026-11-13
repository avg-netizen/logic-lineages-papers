module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FramedContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Proof-side introduction for the exact internal universal. A caller must
provide the actual derivation under arbitrary renamed hypotheses and arbitrary
framed count/value; no native quantified fact is reflected into arithmetic. -/
theorem allIntro (R : Program 2) (job : OTerm alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (count value : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta
     (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R (job.relabel j) count value)) →
   Nonempty (Derivation body Theta (Content R (job.relabel j) value))) :
 Nonempty (Derivation body Delta (AllFramedContent R job)) := by
 unfold AllFramedContent
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold contentMatrix
 let count : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let value : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R (job.relabel Sum.inl) count value
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 obtain ⟨h⟩ := next (alpha ⊕ Fin 2) Sum.inl Theta count value
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentBindingProof
