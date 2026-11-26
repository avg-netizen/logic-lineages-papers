module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalFullFoldSpine OriginalFullFoldSpineSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalStrongInduction InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem atPayloadIntro (data : Data) (window : Program 1) (payload : OrdinaryArithmetic.Term alpha)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix data window payload))) :
    Nonempty (Derivation body Gamma (atPayload data window payload)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 5 Gamma (payloadMatrix data window payload) h

theorem atPayloadApply (data : Data) (window : Program 1)
    (payload input typ out parameter mark : OrdinaryArithmetic.Term alpha)
    (h : Nonempty (Derivation body Gamma (atPayload data window payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 5 Gamma
    (payloadMatrix data window payload) (fun i => emb (![input,typ,out,parameter,mark] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hr) hp⟩

theorem belowPayloadAt (data : Data) (window : Program 1)
    (payload childPayload : OrdinaryArithmetic.Term alpha)
    (h : Nonempty (Derivation body Gamma (belowPayload data window payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayload data window childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate data window)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (data : Data) (window : Program 1)
    (payload childPayload child typ out parameter mark : OrdinaryArithmetic.Term alpha)
    (h : Nonempty (Derivation body Gamma (belowPayload data window payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child)))
    (hp : Nonempty (Derivation body Gamma (premises data window out child typ parameter))) :
    Nonempty (Derivation body Gamma (conclusion out child mark)) :=
  atPayloadApply data window childPayload child typ out parameter mark
    (belowPayloadAt data window payload childPayload h hl) hr hp

/-- Original internal strong induction closes all input and observer variables. -/
theorem payloadInduction (data : Data) (window : Program 1) (payload : OrdinaryArithmetic.Term alpha)
    (step : ∀ (beta : Type) (Delta : List (Formula beta)) (q : OrdinaryArithmetic.Term beta),
      Nonempty (Derivation body Delta (belowPayload data window q)) →
      Nonempty (Derivation body Delta (atPayload data window q))) :
    Nonempty (Derivation body Gamma (atPayload data window payload)) := by
  let theta : Formula (alpha ⊕ Fin 1) := payloadPredicate data window
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate data window))
        (.var (.inr 0)) :: Gamma.map weaken) (atPayload data window (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma (instantiate (payloadPredicate data window) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineBindingProof
