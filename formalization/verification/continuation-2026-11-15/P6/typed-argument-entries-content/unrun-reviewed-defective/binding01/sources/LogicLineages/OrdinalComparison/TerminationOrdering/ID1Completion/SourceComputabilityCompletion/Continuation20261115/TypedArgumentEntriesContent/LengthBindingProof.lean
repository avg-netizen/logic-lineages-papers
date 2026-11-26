module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsLengthBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongLengthInductionSyntaxProof
open LengthInductionDefinitions LengthInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (H : Program 1)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) :=
  InternalClosedProgramsLengthBindingProof.introduction body alpha 6 Delta _ h

theorem atRawApply (input types gamma param entries entryLength typeLength : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H input)))
    (hf : Nonempty (Derivation body Delta (fields H input types gamma param entries entryLength typeLength))) :
    Nonempty (Derivation body Delta (result H input types gamma param entries entryLength typeLength)) := by
  obtain ⟨h⟩ := InternalClosedProgramsLengthBindingProof.elimination body alpha 6 Delta
    (matrix H input) (fun i => emb (![types,gamma,param,entries,entryLength,typeLength] i)) h
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

theorem belowRawApply (input child types gamma param entries entryLength typeLength : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw H input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields H child types gamma param entries entryLength typeLength))) :
    Nonempty (Derivation body Delta (result H child types gamma param entries entryLength typeLength)) :=
  atRawApply H child types gamma param entries entryLength typeLength (belowRawAt H input child h hl) hf

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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthBindingProof
