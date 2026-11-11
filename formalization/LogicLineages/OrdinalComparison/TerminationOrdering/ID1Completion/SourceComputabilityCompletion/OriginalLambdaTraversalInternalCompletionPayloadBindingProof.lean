module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
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

open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem atPayloadIntro (leaf : Program 2) (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix leaf payload))) :
    Nonempty (Derivation body Gamma (AtPayload leaf payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 2 Gamma
    (payloadMatrix leaf payload) h

theorem atPayloadApply (leaf : Program 2) (payload input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (AtPayload leaf payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input))) :
    Nonempty (Derivation body Gamma (HasCompletion leaf input parameter payload)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Gamma
    (payloadMatrix leaf payload) (fun i => emb (![input,parameter] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h hr⟩

theorem belowPayloadAt (leaf : Program 2) (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload leaf payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (AtPayload leaf childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate leaf)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (leaf : Program 2) (payload childPayload child parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload leaf payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child))) :
    Nonempty (Derivation body Gamma (HasCompletion leaf child parameter childPayload)) :=
  atPayloadApply leaf childPayload child parameter
    (belowPayloadAt leaf payload childPayload h hl) hr

/-- The continuation supplies the actual internal induction step at every
context and payload. Strong induction itself is proved in the same calculus. -/
theorem payloadInduction (leaf : Program 2) (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowPayload leaf p)) →
      Nonempty (Derivation body Delta (AtPayload leaf p))) :
    Nonempty (Derivation body Gamma (AtPayload leaf payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate leaf
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate leaf))
        (.var (.inr 0)) :: Gamma.map weaken)
      (AtPayload leaf (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma
    (instantiate (payloadPredicate leaf) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadBindingProof
