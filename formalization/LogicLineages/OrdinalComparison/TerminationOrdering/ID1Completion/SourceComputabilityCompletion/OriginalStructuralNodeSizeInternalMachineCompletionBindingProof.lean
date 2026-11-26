module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationStepPeel (graph5)
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open OriginalHereditaryValidityInternalPushSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundSubst weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open InternalDerivationRenamingSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem completesIntro (d k value count produced : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (completionBody d k value count produced))) :
    Nonempty (Derivation body Gamma (Completes d k value count produced)) :=
  InternalClosedProgramsBindingProof.introduction body α 4 Gamma _ h

theorem completesApply
    (d k value count produced work results initial final : OTerm α)
    (h : Nonempty (Derivation body Gamma (Completes d k value count produced)))
    (hv : Nonempty (Derivation body Gamma
      (graph5 OriginalRawSyntaxTransportInternalMachineState.visitState initial d k value work results)))
    (hr : Nonempty (Derivation body Gamma
      (graph3 OriginalRawSyntaxTransportInternalMachineState.returnState final produced work results))) :
    Nonempty (Derivation body Gamma (graph2 (OriginalStructuralNodeSize.iterate) final count initial)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 4 Gamma
    (completionBody d k value count produced)
    (fun i => emb (![work,results,initial,final] i)) h
  rw [completionBodyWitness] at h
  obtain ⟨hv⟩ := hv
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hv hr)⟩

theorem hasCompletionIntro (d k value payload count produced : OTerm α)
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound count (payloadFuel payload))))
    (hc : Nonempty (Derivation body Gamma (Completes d k value count produced))) :
    Nonempty (Derivation body Gamma (HasCompletion d k value payload)) := by
  apply InternalFiniteBlocksProof.introduction body α 2 Gamma
    (OriginalStructuralNodeSizeInternalMachineCompletion.witnessBody d k value payload) (fun i => emb (![count,produced] i))
  rw [witnessBodyWitness]
  obtain ⟨hb⟩ := hb
  obtain ⟨hc⟩ := hc
  exact ⟨Derivation.conjunctionIntroduction hb hc⟩

theorem hasCompletionCases (d k value payload : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (HasCompletion d k value payload)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (count produced : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (InternalPairingSumBounds.weakBound count (payloadFuel (payload.relabel j)))) →
      Nonempty (Derivation body Delta
        (Completes (d.relabel j) (k.relabel j) (value.relabel j) count produced)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body α 2 Gamma
    (OriginalStructuralNodeSizeInternalMachineCompletion.witnessBody d k value payload) psi h
  let mat := OriginalStructuralNodeSizeInternalMachineCompletion.witnessBody d k value payload
  have hm : Derivation body (mat :: Gamma.map (fun p => p.relabel Sum.inl)) mat :=
    Derivation.hypothesis List.mem_cons_self
  exact step (α ⊕ Fin 2) Sum.inl (mat :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1))
    (by intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft hm⟩ ⟨Derivation.conjunctionRight hm⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
