module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineLeafStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationStepPeel (graph5)
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
open OriginalStructuralNodeSizeInternalMachineIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafComplete (d k value produced : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (hp : Nonempty (Derivation positive Delta (graph3 (constant 3 1) produced d k value))) :
    Nonempty (Derivation positive Delta (Completes d k value (suc z) produced)) := by
  apply completesIntro
  let work : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let stack : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let initial : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let final : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := graph5 visitState initial (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl) work stack ⊓
    graph3 returnState final (produced.relabel Sum.inl) work stack
  let Theta := A :: Delta.map (fun p => p.relabel Sum.inl)
  have hj : ∀ p ∈ Delta, p.relabel Sum.inl ∈ Theta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have ht' := renameInto ht Sum.inl Theta hj
  have hp' := renameInto hp Sum.inl Theta hj
  simp only [graph1Rename,graph3Rename,sucRelabel,zRelabel] at ht' hp'
  have hA : Nonempty (Derivation positive Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := iterateOne initial final
    (OriginalStructuralNodeSizeInternalMachineLeafStepProof.leafBackward initial (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl) work stack (produced.relabel Sum.inl) final
      (andLeft hA) ht' hp' (andRight hA))
  simpa only [completionBody,sucRelabel,zRelabel] using
    (Nonempty.intro (Derivation.implicationIntroduction h))

theorem leafBound (payload : OTerm alpha) :
    Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc z) (payloadFuel payload))) :=
  InternalPairingSumBoundsArithmeticProof.successorWeak z (add payload payload)
    ⟨InternalQuotientComparisonProof.zeroLessSuccessor (add payload payload)⟩

theorem leafHasCompletion (d k value payload produced : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (hp : Nonempty (Derivation positive Delta (graph3 (constant 3 1) produced d k value))) :
    Nonempty (Derivation positive Delta (HasCompletion d k value payload)) :=
  hasCompletionIntro d k value payload (suc z) produced (leafBound payload)
    (leafComplete d k value produced ht hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionLeafProof
