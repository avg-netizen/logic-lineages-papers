module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
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
open OriginalStructuralNodeSizeInternalMachineCompletionRawSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem atRawIntro (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (rawMatrix payload))) :
    Nonempty (Derivation body Gamma (AtRaw payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 2 Gamma
    (rawMatrix payload) h

theorem atRawApply (raw d k : OTerm α)
    (h : Nonempty (Derivation body Gamma (AtRaw raw))) :
    Nonempty (Derivation body Gamma (HasCompletion d k raw raw)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Gamma
    (rawMatrix raw) (fun i => emb (![d,k] i)) h
  rw [rawMatrixWitness] at h
  exact ⟨h⟩

theorem belowRawAt (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowRaw payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (AtRaw childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (rawPredicate)) (emb childPayload)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (raw child d k : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowRaw raw)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Gamma (HasCompletion d k child child)) :=
  atRawApply child d k (belowRawAt raw child h hl)

/-- The continuation supplies the actual internal induction step at every
context and payload. Strong induction itself is proved in the same calculus. -/
theorem rawInduction (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowRaw p)) →
      Nonempty (Derivation body Delta (AtRaw p))) :
    Nonempty (Derivation body Gamma (AtRaw payload)) := by
  let theta : Formula (α ⊕ Fin 1) := rawPredicate
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate))
        (.var (.inr 0)) :: Gamma.map weaken)
      (AtRaw (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma
    (instantiate (rawPredicate) (emb payload)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawBindingProof
