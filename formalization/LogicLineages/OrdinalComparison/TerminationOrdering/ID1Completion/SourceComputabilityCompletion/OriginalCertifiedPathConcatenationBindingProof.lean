module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalCertifiedPathConcatenationDefinitions
open OriginalCertifiedPathConcatenationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {edge : Program 3}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix edge raw))) :
    Nonempty (Derivation body Delta (AtRaw edge raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 5 Delta _ h

theorem atRawApply (input source middle target right combined : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw edge input)))
    (hf : Nonempty (Derivation body Delta (fields edge input source middle target right combined))) :
    Nonempty (Derivation body Delta (result edge source target combined)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 5 Delta
    (matrix edge input) (fun i => emb (![source,middle,target,right,combined] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw edge raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw edge child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate edge)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input child source middle target right combined : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw edge input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields edge child source middle target right combined))) :
    Nonempty (Derivation body Delta (result edge source target combined)) :=
  atRawApply child source middle target right combined (belowRawAt input child h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw edge r)) →
      Nonempty (Derivation body Theta (AtRaw edge r))) :
    Nonempty (Derivation body Delta (AtRaw edge raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate edge
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate edge)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw edge (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate edge) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationBindingProof
