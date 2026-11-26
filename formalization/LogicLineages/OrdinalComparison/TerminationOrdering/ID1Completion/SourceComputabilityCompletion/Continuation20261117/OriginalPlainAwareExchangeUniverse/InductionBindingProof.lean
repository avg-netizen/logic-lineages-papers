module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.MatrixSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Induction InductionSyntaxProof MatrixSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (n : Nat) (arity : Fin n → Nat)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atModeIntro (arguments : Bool) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n arity arguments raw))) :
    Nonempty (Derivation body Delta (AtMode n arity arguments raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 8 Delta _ h

theorem atModeApply (arguments : Bool) (source typ target gamma context symbols types window node : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtMode n arity arguments source))) :
    Nonempty (Derivation body Delta (row n arity arguments source typ target gamma context symbols types window node)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 8 Delta
    (matrix n arity arguments source) (fun i => emb (![typ,target,gamma,context,symbols,types,window,node] i)) h
  rw [matrixWitness] at h
  exact ⟨h⟩

theorem atRawMode (arguments : Bool) (source : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n arity source))) :
    Nonempty (Derivation body Delta (AtMode n arity arguments source)) := by
  cases arguments
  · exact InternalApplicationStepPeelSupportProof.andLeft h
  · exact InternalApplicationStepPeelSupportProof.andRight h

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate n arity)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw n arity r)) →
      Nonempty (Derivation body Theta (AtRaw n arity r))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate n arity
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate n arity)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw n arity (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate n arity) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionBindingProof
