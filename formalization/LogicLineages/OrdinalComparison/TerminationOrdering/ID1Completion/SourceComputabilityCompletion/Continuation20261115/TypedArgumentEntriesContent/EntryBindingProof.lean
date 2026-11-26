module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open EntryInductionDefinitions EntryInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (H : Program 1)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 7 Delta _ h

theorem atRawApply (input types gamma param entries entry tau child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H input)))
    (hf : Nonempty (Derivation body Delta (fields H input types gamma param entries entry tau child))) :
    Nonempty (Derivation body Delta (result H input types gamma param entries entry tau child)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 7 Delta
    (matrix H input) (fun i => emb (![types,gamma,param,entries,entry,tau,child] i)) h
  rw [matrixWitness H] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw H raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw H child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate H)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate H] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input smallerRaw types gamma param entries entry tau child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw H input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess smallerRaw input)))
    (hf : Nonempty (Derivation body Delta (fields H smallerRaw types gamma param entries entry tau child))) :
    Nonempty (Derivation body Delta (result H smallerRaw types gamma param entries entry tau child)) :=
  atRawApply H smallerRaw types gamma param entries entry tau child (belowRawAt H input smallerRaw h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw H r)) →
      Nonempty (Derivation body Theta (AtRaw H r))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate H
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate H)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw H (.var (.inr 0))))
    rw [rawPredicateLift H]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate H) (emb raw)) at e
  rw [rawPredicateInstantiate H] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryBindingProof
