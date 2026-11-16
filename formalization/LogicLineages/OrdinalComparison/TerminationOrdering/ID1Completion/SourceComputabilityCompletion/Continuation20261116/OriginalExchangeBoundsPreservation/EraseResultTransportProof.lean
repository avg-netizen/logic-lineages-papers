module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariantSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseResultTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn emb zSubst sucSubst eqnSubst bindEmbedding liftBind varBind)
open InternalTermSubstitutionProof InternalBinderTransportProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof (conjunctionSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
open EraseInvariant EraseInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem resultSubst {beta : Type} (raw needle bit rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (result raw needle bit rest).subst (fun a => emb (ts a)) =
      result (raw.subst ts) (needle.subst ts) (bit.subst ts) (rest.subst ts) := by
  simp only [result,conjunctionSubst,orSubst,eqnSubst,zSubst,sucSubst,countEffectSubst]

theorem restTransport (raw needle bit rest other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn rest other)))
    (h : Nonempty (Derivation body Delta (result raw needle bit rest))) :
    Nonempty (Derivation body Delta (result raw needle bit other)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (result (raw.relabel Sum.inl) (needle.relabel Sum.inl) (bit.relabel Sum.inl) (.var (.inr 0)))
    (emb rest) (emb other) he
  simp only [instantiate,bindEmbedding,resultSubst,liftBind,varBind] at d
  exact ⟨d h⟩

theorem bitTransport (raw needle bit other rest : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn bit other)))
    (h : Nonempty (Derivation body Delta (result raw needle bit rest))) :
    Nonempty (Derivation body Delta (result raw needle other rest)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (result (raw.relabel Sum.inl) (needle.relabel Sum.inl) (.var (.inr 0)) (rest.relabel Sum.inl))
    (emb bit) (emb other) he
  simp only [instantiate,bindEmbedding,resultSubst,liftBind,varBind] at d
  exact ⟨d h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseResultTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseResultTransportProof
