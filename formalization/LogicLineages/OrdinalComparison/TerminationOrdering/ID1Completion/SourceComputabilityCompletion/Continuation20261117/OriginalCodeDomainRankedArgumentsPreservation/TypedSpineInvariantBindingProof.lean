module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (n : Nat) (H : Program 1) (M W : Program 2)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n H M W raw))) :
    Nonempty (Derivation body Delta (AtRaw n H M W raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 5 Delta _ h

theorem atRawApply (raw count types entries gamma context : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n H M W raw))) :
    Nonempty (Derivation body Delta (row n H M W raw count types entries gamma context)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 5 Delta
    (matrix n H M W raw) (fun i => emb (![count,types,entries,gamma,context] i)) h
  rw [matrixWitness] at h
  exact ⟨h⟩

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw n H M W child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate n H M W)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input smallerRaw count types entries gamma context : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n H M W input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess smallerRaw input))) :
    Nonempty (Derivation body Delta (row n H M W smallerRaw count types entries gamma context)) :=
  atRawApply n H M W smallerRaw count types entries gamma context
    (belowRawAt n H M W input smallerRaw h hl)

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw n H M W r)) →
      Nonempty (Derivation body Theta (AtRaw n H M W r))) :
    Nonempty (Derivation body Delta (AtRaw n H M W raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate n H M W
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate n H M W)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw n H M W (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate n H M W) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantBindingProof
