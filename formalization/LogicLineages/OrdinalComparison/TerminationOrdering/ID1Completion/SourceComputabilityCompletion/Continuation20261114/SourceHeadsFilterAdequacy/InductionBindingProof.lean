module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Induction InductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro (n : Nat) (arity : Fin n → Nat)  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n arity raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 5 Delta _ h

theorem atRawApply (n : Nat) (arity : Fin n → Nat) (input reached candidate parameter out value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n arity input)))
    (hf : Nonempty (Derivation body Delta (fields n arity input reached candidate parameter out value))) :
    Nonempty (Derivation body Delta (result input reached candidate parameter out value)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 5 Delta
    (matrix n arity input) (fun i => emb (![reached,candidate,parameter,out,value] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt (n : Nat) (arity : Fin n → Nat)  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate n arity)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (n : Nat) (arity : Fin n → Nat) (input child reached candidate parameter out value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields n arity child reached candidate parameter out value))) :
    Nonempty (Derivation body Delta (result child reached candidate parameter out value)) :=
  atRawApply n arity child reached candidate parameter out value (belowRawAt n arity input child h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (n : Nat) (arity : Fin n → Nat)  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw n arity r)) →
      Nonempty (Derivation body Theta (AtRaw n arity r))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate E
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate n arity)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw n arity (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate n arity) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionBindingProof
