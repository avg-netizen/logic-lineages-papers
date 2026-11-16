module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open Induction InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph AtFuel

theorem belowSubst {beta : Type} (n : Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (BelowFuel n raw).subst (fun a => emb (ts a)) = BelowFuel n (raw.subst ts) := by
  unfold BelowFuel
  rw [InternalStrongInductionSyntaxProof.belowSubst]
  congr 1
  unfold predicate
  rw [atFuelSubst]
  rfl

theorem belowTransport (n : Nat) (old new : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old new)))
    (h : Nonempty (Derivation body Delta (BelowFuel n old))) :
    Nonempty (Derivation body Delta (BelowFuel n new)) := by
  let F : Formula (alpha ⊕ Fin 1) := BelowFuel n (.var (.inr 0))
  have ht := Derivation.equalityElimination F (emb old) (emb new) (Classical.choice he)
  change Derivation body Delta (instantiate F (emb old)) → Derivation body Delta (instantiate F (emb new)) at ht
  simp only [F,instantiate,bindEmbedding,belowSubst,InternalTagArithmeticSyntaxProof.varBind] at ht
  exact ⟨ht (Classical.choice h)⟩
theorem atTransport (n : Nat) (old new : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old new)))
    (h : Nonempty (Derivation body Delta (AtFuel n old))) :
    Nonempty (Derivation body Delta (AtFuel n new)) := by
  let F : Formula (alpha ⊕ Fin 1) := AtFuel n (.var (.inr 0))
  have ht := Derivation.equalityElimination F (emb old) (emb new) (Classical.choice he)
  change Derivation body Delta (instantiate F (emb old)) → Derivation body Delta (instantiate F (emb new)) at ht
  simp only [F,instantiate,bindEmbedding,atFuelSubst,InternalTagArithmeticSyntaxProof.varBind] at ht
  exact ⟨ht (Classical.choice h)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionTransportProof
