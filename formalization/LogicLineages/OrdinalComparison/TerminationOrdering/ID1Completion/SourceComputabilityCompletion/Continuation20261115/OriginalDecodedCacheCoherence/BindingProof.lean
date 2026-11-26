module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.BindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InductionDefinitions InductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro (n : Nat) (arity : Fin n → Nat) (V : Program 3)  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n arity V raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity V raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 15 Delta _ h

theorem atRawApply (n : Nat) (arity : Fin n → Nat) (V : Program 3) (input node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n arity V input)))
    (hf : Nonempty (Derivation body Delta (fields n arity V input node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found))) :
    Nonempty (Derivation body Delta (result input node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 15 Delta
    (matrix n arity V input) (fun i => emb (![node,param,index1,seed1,rank1,depth1,frontier1,table1,index2,seed2,rank2,depth2,frontier2,table2,found] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt (n : Nat) (arity : Fin n → Nat) (V : Program 3)  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity V raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity V child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate n arity V)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (n : Nat) (arity : Fin n → Nat) (V : Program 3) (input smallerRaw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity V input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess smallerRaw input)))
    (hf : Nonempty (Derivation body Delta (fields n arity V smallerRaw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found))) :
    Nonempty (Derivation body Delta (result smallerRaw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found)) :=
  atRawApply n arity V smallerRaw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found (belowRawAt n arity V input smallerRaw h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (n : Nat) (arity : Fin n → Nat) (V : Program 3)  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw n arity V r)) →
      Nonempty (Derivation body Theta (AtRaw n arity V r))) :
    Nonempty (Derivation body Delta (AtRaw n arity V raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate n arity V
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate n arity V)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw n arity V (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate n arity V) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.BindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.BindingProof
