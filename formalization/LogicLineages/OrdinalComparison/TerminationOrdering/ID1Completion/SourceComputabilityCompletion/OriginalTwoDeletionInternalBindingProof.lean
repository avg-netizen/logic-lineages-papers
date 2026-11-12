module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalTwoDeletionInternal OriginalTwoDeletionInternalSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro (p : Program 3) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (commutationMatrix p raw))) :
    Nonempty (Derivation body Delta (AtRaw p raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 8 Delta _ h

theorem atRawApply (p : Program 3) (raw a b i j upper lower left right : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw p raw)))
    (hg : Nonempty (Derivation body Delta (fields p raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 8 Delta
    (commutationMatrix p raw) (fun k => emb (![a,b,i,j,upper,lower,left,right] k)) h
  rw [commutationMatrixWitness] at h
  obtain ⟨hg⟩ := hg
  exact ⟨Derivation.implicationElimination h hg⟩

theorem belowRawAt (p : Program 3) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw p raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw p child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate p)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (p : Program 3) (raw child a b i j upper lower left right : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw p raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hg : Nonempty (Derivation body Delta (fields p child a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) :=
  atRawApply p child a b i j upper lower left right (belowRawAt p raw child h hl) hg

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (p : Program 3) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw p r)) →
      Nonempty (Derivation body Theta (AtRaw p r))) :
    Nonempty (Derivation body Delta (AtRaw p raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate p
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate p)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw p (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate p) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
