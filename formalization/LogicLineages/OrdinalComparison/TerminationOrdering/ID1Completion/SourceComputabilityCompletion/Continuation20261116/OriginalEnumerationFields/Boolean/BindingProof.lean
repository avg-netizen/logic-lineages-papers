module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.BindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open SyntaxProof
open Continuation20261114.HeadWindowBooleanRange
open InternalApplicationStepPeelSupportProof (andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRankIntro (n : Nat) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n raw))) :
    Nonempty (Derivation body Delta (AtRank n raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 3 Delta _ h

theorem atRankApply (n : Nat) (raw key param out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRank n raw)))
    (hf : Nonempty (Derivation body Delta (graph2 rank raw key param ⊓ graph2 (extract n) out key param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
    (matrix n raw) (fun i => emb ((![key,param,out] : Fin 3 → OTerm alpha) i)) h
  rw [SyntaxProof.matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRankAt (n : Nat) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRank n raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRank n child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate n)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rankInduction (n : Nat) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRank n r)) →
      Nonempty (Derivation body Theta (AtRank n r))) :
    Nonempty (Derivation body Delta (AtRank n raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate n
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate n)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRank n (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate n) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.BindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.BindingProof
