module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open OriginalRawSyntaxTransportInternalParameters OriginalRawSyntaxTransportInternalParametersSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro (p : Program 3) (rank : Bool) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (parameterMatrix p rank raw))) :
    Nonempty (Derivation body Delta (AtRaw p rank raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 5 Delta _ h

theorem atRawApply (p : Program 3) (rank : Bool) (raw out d k other otherK : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw p rank raw)))
    (hg : Nonempty (Derivation body Delta (graph3 p out d k raw))) :
    Nonempty (Derivation body Delta (graph3 p out other (if rank then otherK else k) raw)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 5 Delta
    (parameterMatrix p rank raw) (fun i => emb (![out,d,k,other,otherK] i)) h
  rw [parameterMatrixWitness] at h
  obtain ⟨hg⟩ := hg
  exact ⟨Derivation.implicationElimination h hg⟩

theorem belowRawAt (p : Program 3) (rank : Bool) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw p rank raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw p rank child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate p rank)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (p : Program 3) (rank : Bool) (raw child out d k other otherK : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw p rank raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hg : Nonempty (Derivation body Delta (graph3 p out d k child))) :
    Nonempty (Derivation body Delta (graph3 p out other (if rank then otherK else k) child)) :=
  atRawApply p rank child out d k other otherK (belowRawAt p rank raw child h hl) hg

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (p : Program 3) (rank : Bool) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw p rank r)) →
      Nonempty (Derivation body Theta (AtRaw p rank r))) :
    Nonempty (Derivation body Delta (AtRaw p rank raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate p rank
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate p rank)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw p rank (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate p rank) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
