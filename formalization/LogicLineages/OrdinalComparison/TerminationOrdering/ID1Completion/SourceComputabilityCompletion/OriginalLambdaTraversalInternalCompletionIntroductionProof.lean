module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem completesByRuns (leaf : Program 2) (value parameter count produced : OTerm alpha)
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (work stack start finish : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta
        (graph4 visitState start (value.relabel j) (parameter.relabel j) work stack)) →
      Nonempty (Derivation positive Theta (graph3 returnState finish (produced.relabel j) work stack)) →
      Nonempty (Derivation positive Theta (graph2 (iterate leaf) finish (count.relabel j) start))) :
    Nonempty (Derivation positive Delta (Completes leaf value parameter count produced)) := by
  apply completesIntro
  let work : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let stack : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let start : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let finish : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := graph4 visitState start (value.relabel Sum.inl) (parameter.relabel Sum.inl) work stack ⊓
    graph3 returnState finish (produced.relabel Sum.inl) work stack
  let Theta := A :: Delta.map (fun p => p.relabel Sum.inl)
  have hj : ∀ p ∈ Delta, p.relabel Sum.inl ∈ Theta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hA : Nonempty (Derivation positive Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := k (alpha ⊕ Fin 4) Sum.inl Theta work stack start finish hj (andLeft hA) (andRight hA)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionIntroductionProof
