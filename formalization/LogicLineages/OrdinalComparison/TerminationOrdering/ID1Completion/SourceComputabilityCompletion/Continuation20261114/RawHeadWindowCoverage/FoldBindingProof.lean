module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Fold FoldSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

variable {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+1))
theorem atRawIntro (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix base step transform raw))) :
    Nonempty (Derivation body Delta (AtRaw base step transform raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha (k+3) Delta _ h

theorem atRawApply (raw needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw base step transform raw)))
    (hf : Nonempty (Derivation body Delta (fields base step transform raw needle image out params))) :
    Nonempty (Derivation body Delta (result out image)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha (k+3) Delta
    (matrix base step transform raw) (fun i => emb (Fin.cons needle (Fin.cons image (Fin.cons out params)) i)) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw base step transform child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate base step transform)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (raw child needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hf : Nonempty (Derivation body Delta (fields base step transform child needle image out params))) :
    Nonempty (Derivation body Delta (result out image)) :=
  atRawApply base step transform child needle image out params (belowRawAt base step transform raw child h hl) hf

theorem rawInduction (raw : OTerm alpha)
    (advance : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw base step transform r)) →
      Nonempty (Derivation body Theta (AtRaw base step transform r))) :
    Nonempty (Derivation body Delta (AtRaw base step transform raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate base step transform
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate base step transform)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw base step transform (.var (.inr 0))))
    rw [rawPredicateLift]
    exact advance (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate base step transform) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldBindingProof
