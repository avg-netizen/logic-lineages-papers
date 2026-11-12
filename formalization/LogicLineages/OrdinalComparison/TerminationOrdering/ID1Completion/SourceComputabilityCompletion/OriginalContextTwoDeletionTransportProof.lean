module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding)
open InternalTagArithmeticSupportProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextTwoDeletionInductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsLater (gamma count i a b upper lower left right old new : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old new)))
    (hf : Nonempty (Derivation body Delta (fields gamma count i old a b upper lower left right))) :
    Nonempty (Derivation body Delta (fields gamma count i new a b upper lower left right)) := by
  let F : Formula (alpha ⊕ Fin 1) := fields (gamma.relabel Sum.inl) (count.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0)) (a.relabel Sum.inl) (b.relabel Sum.inl) (upper.relabel Sum.inl) (lower.relabel Sum.inl) (left.relabel Sum.inl) (right.relabel Sum.inl)
  obtain ⟨he⟩ := he
  obtain ⟨hf⟩ := hf
  have h := Derivation.equalityElimination F (emb old) (emb new) he
  change Derivation body Delta (instantiate F (emb old)) →
    Derivation body Delta (instantiate F (emb new)) at h
  simp only [F,instantiate,bindEmbedding,fieldsSubst,
    InternalTagArithmeticSyntaxProof.liftBind,InternalTagArithmeticSyntaxProof.varBind] at h
  exact ⟨h hf⟩

theorem resultLater (i a b upper lower left right old new : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old new)))
    (hf : Nonempty (Derivation body Delta (result i old a b upper lower left right))) :
    Nonempty (Derivation body Delta (result i new a b upper lower left right)) := by
  let F : Formula (alpha ⊕ Fin 1) := result (i.relabel Sum.inl) (.var (.inr 0)) (a.relabel Sum.inl) (b.relabel Sum.inl) (upper.relabel Sum.inl) (lower.relabel Sum.inl) (left.relabel Sum.inl) (right.relabel Sum.inl)
  obtain ⟨he⟩ := he
  obtain ⟨hf⟩ := hf
  have h := Derivation.equalityElimination F (emb old) (emb new) he
  change Derivation body Delta (instantiate F (emb old)) →
    Derivation body Delta (instantiate F (emb new)) at h
  simp only [F,instantiate,bindEmbedding,resultSubst,
    InternalTagArithmeticSyntaxProof.liftBind,InternalTagArithmeticSyntaxProof.varBind] at h
  exact ⟨h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTransportProof
