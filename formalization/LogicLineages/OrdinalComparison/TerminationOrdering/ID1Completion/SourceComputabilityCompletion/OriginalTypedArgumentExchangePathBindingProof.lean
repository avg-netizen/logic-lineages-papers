module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalTypedArgumentExchangePathInductionDefinitions OriginalTypedArgumentExchangePathSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {R : Program 2}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix R raw))) :
    Nonempty (Derivation body Delta (AtRaw R raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 6 Delta _ h

theorem atRawApply (input source target value newSource newTarget mapped : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw R input)))
    (hf : Nonempty (Derivation body Delta (fields R input source target value newSource newTarget mapped))) :
    Nonempty (Derivation body Delta (result newSource newTarget mapped)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 6 Delta
    (matrix R input) (fun i => emb (![source,target,value,newSource,newTarget,mapped] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw R raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw R child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate R)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input child source target value newSource newTarget mapped : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw R input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields R child source target value newSource newTarget mapped))) :
    Nonempty (Derivation body Delta (result newSource newTarget mapped)) :=
  atRawApply child source target value newSource newTarget mapped (belowRawAt input child h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw R r)) →
      Nonempty (Derivation body Theta (AtRaw R r))) :
    Nonempty (Derivation body Delta (AtRaw R raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate R
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate R)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw R (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate R) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathBindingProof
