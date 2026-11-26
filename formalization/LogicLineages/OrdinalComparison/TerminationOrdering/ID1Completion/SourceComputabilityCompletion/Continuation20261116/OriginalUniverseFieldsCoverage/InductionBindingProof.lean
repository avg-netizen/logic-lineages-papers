module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] InternalControlGraph.programGraph

theorem atModeIntro (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n arity H arguments raw))) :
    Nonempty (Derivation body Delta (AtMode n arity H arguments raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 11 Delta (matrix n arity H arguments raw) h

theorem atModeApply (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtMode n arity H arguments raw)))
    (hf : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (result n arguments raw xs)) := by
  obtain ⟨hi⟩ := InternalClosedProgramsBindingProof.elimination body alpha 11 Delta
    (matrix n arity H arguments raw) (fun i => emb (xs i)) h
  rw [InductionWitnessProof.matrixWitness] at hi
  exact ⟨Derivation.implicationElimination hi (Classical.choice hf)⟩

theorem atRawApply (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n arity H raw)))
    (hf : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (result n arguments raw xs)) := by
  cases arguments
  · exact atModeApply n arity H false raw xs (andLeft h) hf
  · exact atModeApply n arity H true raw xs (andRight h) hf

theorem belowRawAt (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n arity H raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity H child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate n arity H)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw n arity H r)) →
      Nonempty (Derivation body Theta (AtRaw n arity H r))) :
    Nonempty (Derivation body Delta (AtRaw n arity H raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate n arity H
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate n arity H)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw n arity H (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate n arity H) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionBindingProof
