module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InductionDefinitions InductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro (D : Program 2) (G : Program 3)  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix D G raw))) :
    Nonempty (Derivation body Delta (AtRaw D G raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 7 Delta _ h

theorem atRawApply (D : Program 2) (G : Program 3) (input query old param deps answers value out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw D G input)))
    (hf : Nonempty (Derivation body Delta (fields D G input query old param deps answers value out))) :
    Nonempty (Derivation body Delta (result query value out)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 7 Delta
    (matrix D G input) (fun i => emb (![query,old,param,deps,answers,value,out] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt (D : Program 2) (G : Program 3)  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw D G child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate D G)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (D : Program 2) (G : Program 3) (input child query old param deps answers value out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw D G input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields D G child query old param deps answers value out))) :
    Nonempty (Derivation body Delta (result query value out)) :=
  atRawApply D G child query old param deps answers value out (belowRawAt D G input child h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (D : Program 2) (G : Program 3)  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw D G r)) →
      Nonempty (Derivation body Theta (AtRaw D G r))) :
    Nonempty (Derivation body Delta (AtRaw D G raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate D G
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate D G)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw D G (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate D G) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionBindingProof
