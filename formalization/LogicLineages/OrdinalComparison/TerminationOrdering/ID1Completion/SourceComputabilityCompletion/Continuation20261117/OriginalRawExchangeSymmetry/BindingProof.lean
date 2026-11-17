module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (n : Nat) (arity : Fin n → Nat)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n arity raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 6 Delta _ h

theorem atRawApply (input target node rev window symbols types : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n arity input)))
    (hf : Nonempty (Derivation body Delta (fields n arity input target node rev window symbols types))) :
    Nonempty (Derivation body Delta (graph2 (Continuation20261115.OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 6 Delta
    (matrix n arity input) (fun i => emb (![target,node,rev,window,symbols,types] i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

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

theorem belowRawApply (input smallerRaw target node rev window symbols types : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess smallerRaw input)))
    (hf : Nonempty (Derivation body Delta (fields n arity smallerRaw target node rev window symbols types))) :
    Nonempty (Derivation body Delta (graph2 (Continuation20261115.OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) :=
  atRawApply n arity smallerRaw target node rev window symbols types (belowRawAt n arity input smallerRaw h hl) hf

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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BindingProof
