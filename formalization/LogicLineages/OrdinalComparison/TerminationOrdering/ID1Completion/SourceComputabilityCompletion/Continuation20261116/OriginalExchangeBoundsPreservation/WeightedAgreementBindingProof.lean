module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open WeightedAgreement WeightedAgreementSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (weight : Program 1)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix weight raw))) :
    Nonempty (Derivation body Delta (AtRaw weight raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 3 Delta _ h

theorem atRawApply (input right ls rs : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw weight input)))
    (hf : Nonempty (Derivation body Delta (fields weight input right ls rs))) :
    Nonempty (Derivation body Delta (eqn ls rs)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
    (matrix weight input) (fun i => emb (![right,ls,rs] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw weight raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw weight child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate weight)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input smallerRaw right ls rs : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw weight input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess smallerRaw input)))
    (hf : Nonempty (Derivation body Delta (fields weight smallerRaw right ls rs))) :
    Nonempty (Derivation body Delta (eqn ls rs)) :=
  atRawApply weight smallerRaw right ls rs (belowRawAt weight input smallerRaw h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw weight r)) →
      Nonempty (Derivation body Theta (AtRaw weight r))) :
    Nonempty (Derivation body Delta (AtRaw weight raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate weight
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate weight)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw weight (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate weight) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementBindingProof
