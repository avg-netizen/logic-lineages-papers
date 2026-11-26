module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn emb zSubst sucSubst eqnSubst bindEmbedding liftBind varBind)
open InternalTermSubstitutionProof InternalBinderTransportProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof (conjunctionSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
open WeightedErase WeightedEraseSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem bitTransport (bit total remainingWeight needleWeight other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn bit other)))
    (h : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (effect other total remainingWeight needleWeight)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (effect (.var (.inr 0)) (total.relabel Sum.inl) (remainingWeight.relabel Sum.inl) (needleWeight.relabel Sum.inl)) (emb bit) (emb other) he
  simp only [instantiate,bindEmbedding,effectSubst,liftBind,varBind] at d
  exact ⟨d h⟩

theorem totalTransport (bit total remainingWeight needleWeight other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn total other)))
    (h : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (effect bit other remainingWeight needleWeight)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (effect (bit.relabel Sum.inl) (.var (.inr 0)) (remainingWeight.relabel Sum.inl) (needleWeight.relabel Sum.inl)) (emb total) (emb other) he
  simp only [instantiate,bindEmbedding,effectSubst,liftBind,varBind] at d
  exact ⟨d h⟩

theorem remainingWeightTransport (bit total remainingWeight needleWeight other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn remainingWeight other)))
    (h : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (effect bit total other needleWeight)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (effect (bit.relabel Sum.inl) (total.relabel Sum.inl) (.var (.inr 0)) (needleWeight.relabel Sum.inl)) (emb remainingWeight) (emb other) he
  simp only [instantiate,bindEmbedding,effectSubst,liftBind,varBind] at d
  exact ⟨d h⟩

theorem needleWeightTransport (bit total remainingWeight needleWeight other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn needleWeight other)))
    (h : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (effect bit total remainingWeight other)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (effect (bit.relabel Sum.inl) (total.relabel Sum.inl) (remainingWeight.relabel Sum.inl) (.var (.inr 0))) (emb needleWeight) (emb other) he
  simp only [instantiate,bindEmbedding,effectSubst,liftBind,varBind] at d
  exact ⟨d h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseTransportProof
