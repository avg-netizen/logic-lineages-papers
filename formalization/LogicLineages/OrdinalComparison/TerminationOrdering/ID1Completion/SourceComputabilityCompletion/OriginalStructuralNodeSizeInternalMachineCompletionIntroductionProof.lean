module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationStepPeel (graph5)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem completesByRuns (d k value count produced : OTerm alpha)
    (cont : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (work stack start finish : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta
        (graph5 visitState start (d.relabel j) (k.relabel j) (value.relabel j) work stack)) →
      Nonempty (Derivation positive Theta (graph3 returnState finish (produced.relabel j) work stack)) →
      Nonempty (Derivation positive Theta (graph2 (OriginalStructuralNodeSize.iterate) finish (count.relabel j) start))) :
    Nonempty (Derivation positive Delta (Completes d k value count produced)) := by
  apply completesIntro
  let work : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let stack : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let start : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let finish : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := graph5 visitState start (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl) work stack ⊓
    graph3 returnState finish (produced.relabel Sum.inl) work stack
  let Theta := A :: Delta.map (fun p => p.relabel Sum.inl)
  have hj : ∀ p ∈ Delta, p.relabel Sum.inl ∈ Theta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hA : Nonempty (Derivation positive Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := cont (alpha ⊕ Fin 4) Sum.inl Theta work stack start finish hj (andLeft hA) (andRight hA)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
