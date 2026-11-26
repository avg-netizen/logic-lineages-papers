module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open EvaluatorKeyCanonicalInductionDefinitions EvaluatorKeyCanonicalSyntaxProof
open UniformCertificateCompletion
open InternalOriginalUniformDescentSelection (Data)
open InternalStrongInduction InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem atPayloadIntro (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) (payload : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix p H G W P payload))) :
    Nonempty (Derivation body Gamma (atPayload p H G W P payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 5 Gamma (payloadMatrix p H G W P payload) h

theorem atPayloadApply (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload left right leftOut rightOut parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (atPayload p H G W P payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload left)))
    (hp : Nonempty (Derivation body Gamma (Premises p H G W P left right leftOut rightOut parameter))) :
    Nonempty (Derivation body Gamma (equal leftOut rightOut)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 5 Gamma
    (payloadMatrix p H G W P payload) (fun i => emb (![left,right,leftOut,rightOut,parameter] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hr) hp⟩

theorem belowPayloadAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload childPayload : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (belowPayload p H G W P payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayload p H G W P childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate p H G W P)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload childPayload child otherChild childOut otherOut parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (belowPayload p H G W P payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child)))
    (hp : Nonempty (Derivation body Gamma (Premises p H G W P child otherChild childOut otherOut parameter))) :
    Nonempty (Derivation body Gamma (equal childOut otherOut)) :=
  atPayloadApply p H G W P childPayload child otherChild childOut otherOut parameter
    (belowPayloadAt p H G W P payload childPayload h hl) hr hp

/-- All five input/type/output/parameter/value variables stay inside induction. -/
theorem payloadInduction (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) (payload : OrdinaryArithmetic.Term α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (q : OrdinaryArithmetic.Term β),
      Nonempty (Derivation body Delta (belowPayload p H G W P q)) →
      Nonempty (Derivation body Delta (atPayload p H G W P q))) :
    Nonempty (Derivation body Gamma (atPayload p H G W P payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate p H G W P
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate p H G W P))
        (.var (.inr 0)) :: Gamma.map weaken) (atPayload p H G W P (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma (instantiate (payloadPredicate p H G W P) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalBindingProof
