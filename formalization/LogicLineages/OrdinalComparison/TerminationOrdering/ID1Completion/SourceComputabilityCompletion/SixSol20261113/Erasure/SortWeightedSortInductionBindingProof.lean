module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open SortWeightedSortInductionDefinitions SortWeightedSortInductionSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {k : Nat} (F : Program (k+1))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha) (params : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix F raw params))) :
    Nonempty (Derivation body Delta (AtRaw F raw params)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 2 Delta _ h

theorem atRawApply (input sorted sum : OTerm alpha) (params : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw F input params)))
    (hf : Nonempty (Derivation body Delta (fields F input sorted sum params))) :
    Nonempty (Derivation body Delta (result F sorted sum params)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 2 Delta
    (matrix F input params) (fun i => emb (![sorted,sum] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt  (raw child : OTerm alpha) (params : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw F raw params)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw F child params)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate F params)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input child sorted sum : OTerm alpha) (params : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw F input params)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields F child sorted sum params))) :
    Nonempty (Derivation body Delta (result F sorted sum params)) :=
  atRawApply F child sorted sum params (belowRawAt F input child params h hl) hf

/-- All free weighting parameters survive the original internal induction. -/
theorem rawInduction (raw : OTerm alpha) (params : Fin k → OTerm alpha)
 (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta)
   (ps : Fin k → OTerm beta),
   Nonempty (Derivation body Theta (BelowRaw F r ps)) →
   Nonempty (Derivation body Theta (AtRaw F r ps))) :
 Nonempty (Derivation body Delta (AtRaw F raw params)) := by
 let theta : Formula (alpha ⊕ Fin 1) := rawPredicate F params
 have hs : Nonempty (Derivation body
   (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
   change Nonempty (Derivation body
     (InternalStrongInduction.below (lift (rawPredicate F params)) (.var (.inr 0)) :: Delta.map weaken)
     (AtRaw F (.var (.inr 0)) (fun i => (params i).relabel Sum.inl)))
   rw [rawPredicateLift]
   exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) _ ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨d⟩ := strongInduction theta hs
 have e := Derivation.universalElimination (emb raw) d
 change Derivation body Delta (instantiate (rawPredicate F params) (emb raw)) at e
 rw [rawPredicateInstantiate] at e
 exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionBindingProof
