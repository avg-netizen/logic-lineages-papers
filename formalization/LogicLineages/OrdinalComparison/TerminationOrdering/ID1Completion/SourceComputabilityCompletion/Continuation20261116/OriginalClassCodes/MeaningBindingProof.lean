module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Meaning MeaningSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem introduce (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (Targets.meaning n arity H seed param candidate)) := by
  rw [frozenBlock]
  apply InternalFiniteBlocksProof.introduction body alpha 9 Delta _ (fun i => emb (xs i))
  rw [matrixWitness]
  exact h

theorem cases (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (Targets.meaning n arity H seed param candidate)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (xs : Fin 9 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (observations n arity H (seed.relabel j) (param.relabel j) (candidate.relabel j) xs)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  rw [frozenBlock] at h
  apply InternalFiniteBlocksProof.elimination body alpha 9 Delta (matrix n arity H seed param candidate) psi h
  let Theta := matrix n arity H seed param candidate :: Delta.map (fun q => q.relabel Sum.inl)
  exact next (alpha ⊕ Fin 9) Sum.inl Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningBindingProof
