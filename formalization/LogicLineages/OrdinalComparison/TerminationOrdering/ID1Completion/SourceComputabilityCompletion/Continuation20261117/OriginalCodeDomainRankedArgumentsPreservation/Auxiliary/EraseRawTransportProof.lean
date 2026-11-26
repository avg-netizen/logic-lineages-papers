module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseInvariantSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseResultTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseRawTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn emb zSubst sucSubst eqnSubst bindEmbedding liftBind varBind)
open InternalTermSubstitutionProof InternalBinderTransportProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof (conjunctionSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
open EraseInvariant EraseInvariantSyntaxProof EraseResultTransportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawTransport (raw other needle bit rest : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw other)))
    (h : Nonempty (Derivation body Delta (result raw needle bit rest))) :
    Nonempty (Derivation body Delta (result other needle bit rest)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (result (.var (.inr 0)) (needle.relabel Sum.inl) (bit.relabel Sum.inl) (rest.relabel Sum.inl))
    (emb raw) (emb other) he
  simp only [instantiate,bindEmbedding,resultSubst,liftBind,varBind] at d
  exact ⟨d h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseRawTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseRawTransportProof
