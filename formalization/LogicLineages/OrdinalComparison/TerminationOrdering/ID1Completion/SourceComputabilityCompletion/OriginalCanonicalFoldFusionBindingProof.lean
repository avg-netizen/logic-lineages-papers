module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion OriginalCanonicalFoldFusionSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalStrongInduction InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem atPayloadIntro (data : Data) (window : Program 1) (source target : Program 2) (payload : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix data window source target payload))) :
    Nonempty (Derivation body Gamma (atPayload data window source target payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 4 Gamma (payloadMatrix data window source target payload) h

theorem atPayloadApply (data : Data) (window : Program 1) (source target : Program 2)
    (payload input typ out parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (atPayload data window source target payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hp : Nonempty (Derivation body Gamma (premises data window source target out input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out input typ parameter)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 4 Gamma
    (payloadMatrix data window source target payload) (fun i => emb (![input,typ,out,parameter] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hr) hp⟩

theorem belowPayloadAt (data : Data) (window : Program 1) (source target : Program 2)
    (payload childPayload : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (belowPayload data window source target payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayload data window source target childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate data window source target)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (data : Data) (window : Program 1) (source target : Program 2)
    (payload childPayload child typ out parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (belowPayload data window source target payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child)))
    (hp : Nonempty (Derivation body Gamma (premises data window source target out child typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out child typ parameter)) :=
  atPayloadApply data window source target childPayload child typ out parameter
    (belowPayloadAt data window source target payload childPayload h hl) hr hp

/-- All four input/type/output/parameter variables stay inside the invariant. -/
theorem payloadInduction (data : Data) (window : Program 1) (source target : Program 2) (payload : OrdinaryArithmetic.Term α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OrdinaryArithmetic.Term β),
      Nonempty (Derivation body Delta (belowPayload data window source target p)) →
      Nonempty (Derivation body Delta (atPayload data window source target p))) :
    Nonempty (Derivation body Gamma (atPayload data window source target payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate data window source target
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate data window source target))
        (.var (.inr 0)) :: Gamma.map weaken) (atPayload data window source target (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma (instantiate (payloadPredicate data window source target) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionBindingProof
