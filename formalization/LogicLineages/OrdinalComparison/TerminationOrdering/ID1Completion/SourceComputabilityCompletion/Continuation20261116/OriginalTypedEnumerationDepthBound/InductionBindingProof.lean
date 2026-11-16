module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] InternalControlGraph.programGraph

theorem atModeIntro (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n H arguments raw))) :
    Nonempty (Derivation body Delta (AtMode n H arguments raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 6 Delta (matrix n H arguments raw) h

theorem atModeApply (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 6 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtMode n H arguments raw)))
    (hf : Nonempty (Derivation body Delta (observations n H arguments raw xs))) :
    Nonempty (Derivation body Delta (result arguments (xs 3) (xs 5))) := by
  obtain ⟨hi⟩ := InternalClosedProgramsBindingProof.elimination body alpha 6 Delta
    (matrix n H arguments raw) (fun i => emb (xs i)) h
  rw [InductionWitnessProof.matrixWitness] at hi
  exact ⟨Derivation.implicationElimination hi (Classical.choice hf)⟩

theorem atRawApply (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 6 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw n H raw)))
    (hf : Nonempty (Derivation body Delta (observations n H arguments raw xs))) :
    Nonempty (Derivation body Delta (result arguments (xs 3) (xs 5))) := by
  cases arguments
  · exact atModeApply n H false raw xs (andLeft h) hf
  · exact atModeApply n H true raw xs (andRight h) hf

theorem belowRawAt (n : Nat) (H : Program 1) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw n H raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw n H child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate n H)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction (n : Nat) (H : Program 1) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw n H r)) →
      Nonempty (Derivation body Theta (AtRaw n H r))) :
    Nonempty (Derivation body Delta (AtRaw n H raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate n H
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate n H)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw n H (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate n H) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionBindingProof
