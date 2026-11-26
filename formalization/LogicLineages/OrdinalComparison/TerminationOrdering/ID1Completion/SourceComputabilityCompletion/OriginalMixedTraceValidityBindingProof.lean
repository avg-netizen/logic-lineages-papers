module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValiditySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalMixedTraceValidityDefinitions OriginalMixedTraceValiditySyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atPathIntro (source : Program 2) (leaf : Program 4) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix source leaf raw))) :
    Nonempty (Derivation body Delta (AtPath source leaf raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 4 Delta _ h

theorem atPathApply (source : Program 2) (leaf : Program 4) (raw s t cert oldParam : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtPath source leaf raw)))
    (hg : Nonempty (Derivation body Delta (fields source leaf raw s t cert oldParam ))) :
    Nonempty (Derivation body Delta (result source leaf t oldParam)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 4 Delta
    (matrix source leaf raw) (fun k => emb (![s,t,cert,oldParam] k)) h
  rw [matrixWitness] at h
  obtain ⟨hg⟩ := hg
  exact ⟨Derivation.implicationElimination h hg⟩

theorem belowPathAt (source : Program 2) (leaf : Program 4) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowPath source leaf raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtPath source leaf child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have drv :=  Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (pathPredicate source leaf)) (emb child)) at drv
  rw [belowElimSyntax,pathPredicateInstantiate] at drv
  exact ⟨Derivation.implicationElimination drv hl⟩

theorem belowPathApply (source : Program 2) (leaf : Program 4) (raw child s t cert oldParam : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowPath source leaf raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hg : Nonempty (Derivation body Delta (fields source leaf child s t cert oldParam ))) :
    Nonempty (Derivation body Delta (result source leaf t oldParam)) :=
  atPathApply source leaf child s t cert oldParam (belowPathAt source leaf raw child h hl) hg

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem pathInduction (source : Program 2) (leaf : Program 4) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowPath source leaf r)) →
      Nonempty (Derivation body Theta (AtPath source leaf r))) :
    Nonempty (Derivation body Delta (AtPath source leaf raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := pathPredicate source leaf
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (pathPredicate source leaf)) (.var (.inr 0)) :: Delta.map weaken)
      (AtPath source leaf (.var (.inr 0))))
    rw [pathPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨drv⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) drv
  change Derivation body Delta (instantiate (pathPredicate source leaf) (emb raw)) at e
  rw [pathPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityBindingProof
