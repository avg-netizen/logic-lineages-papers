module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionBindingProof
open OriginalLambdaTraversalInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafComplete (leaf : Program 2) (value parameter produced : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value)))
    (hp : Nonempty (Derivation positive Delta (graph2 leaf produced value parameter))) :
    Nonempty (Derivation positive Delta (Completes leaf value parameter (suc z) produced)) := by
  apply completesIntro
  let work : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let stack : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let initial : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let final : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := graph4 visitState initial (value.relabel Sum.inl) (parameter.relabel Sum.inl) work stack ⊓
    graph3 returnState final (produced.relabel Sum.inl) work stack
  let Theta := A :: Delta.map (fun p => p.relabel Sum.inl)
  have hj : ∀ p ∈ Delta, p.relabel Sum.inl ∈ Theta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have ht' := renameInto ht Sum.inl Theta hj
  have hp' := renameInto hp Sum.inl Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at ht' hp'
  have hA : Nonempty (Derivation positive Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := iterateOne leaf initial final
    (OriginalLambdaTraversalInternalLeafStepProof.leafBackward leaf initial (value.relabel Sum.inl)
      (parameter.relabel Sum.inl) work stack (produced.relabel Sum.inl) final
      (andLeft hA) ht' hp' (andRight hA))
  simpa only [completionBody,sucRelabel,zRelabel] using
    (Nonempty.intro (Derivation.implicationIntroduction h))

theorem leafBound (payload : OTerm alpha) :
    Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc z) (payloadFuel payload))) :=
  InternalPairingSumBoundsArithmeticProof.successorWeak z (add payload payload)
    ⟨InternalQuotientComparisonProof.zeroLessSuccessor (add payload payload)⟩

theorem leafHasCompletion (leaf : Program 2) (value parameter payload produced : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value)))
    (hp : Nonempty (Derivation positive Delta (graph2 leaf produced value parameter))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) :=
  hasCompletionIntro leaf value parameter payload (suc z) produced (leafBound payload)
    (leafComplete leaf value parameter produced ht hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLeafProof
