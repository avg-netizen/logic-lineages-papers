module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawBindingProof
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

open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionRawSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem atRawIntro (mode : Mode) (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (rawMatrix mode payload))) :
    Nonempty (Derivation body Gamma (AtRaw mode payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 2 Gamma
    (rawMatrix mode payload) h

theorem atRawApply (mode : Mode) (raw d k : OTerm α)
    (h : Nonempty (Derivation body Gamma (AtRaw mode raw))) :
    Nonempty (Derivation body Gamma (HasCompletion mode d k raw raw)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Gamma
    (rawMatrix mode raw) (fun i => emb (![d,k] i)) h
  rw [rawMatrixWitness] at h
  exact ⟨h⟩

theorem belowRawAt (mode : Mode) (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowRaw mode payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (AtRaw mode childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (rawPredicate mode)) (emb childPayload)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (mode : Mode) (raw child d k : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowRaw mode raw)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Gamma (HasCompletion mode d k child child)) :=
  atRawApply mode child d k (belowRawAt mode raw child h hl)

/-- The continuation supplies the actual internal induction step at every
context and payload. Strong induction itself is proved in the same calculus. -/
theorem rawInduction (mode : Mode) (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowRaw mode p)) →
      Nonempty (Derivation body Delta (AtRaw mode p))) :
    Nonempty (Derivation body Gamma (AtRaw mode payload)) := by
  let theta : Formula (α ⊕ Fin 1) := rawPredicate mode
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate mode))
        (.var (.inr 0)) :: Gamma.map weaken)
      (AtRaw mode (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma
    (instantiate (rawPredicate mode) (emb payload)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawBindingProof
