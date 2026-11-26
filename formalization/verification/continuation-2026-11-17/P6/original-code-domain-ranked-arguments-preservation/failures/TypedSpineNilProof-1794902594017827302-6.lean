module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb bindEmbedding liftBind varBind)
open InternalTagArithmeticSupportProof (cancelSuc symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem entriesZero (raw entries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z))) :
    Nonempty (Derivation body Delta (eqn entries z)) := by
  obtain ⟨h⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) (suc z) ![raw,z] he
    (ArgumentEntriesNilExtraction.Proof.nilExtraction body alpha Delta raw z hc)
  exact ⟨cancelSuc h⟩

theorem nilGood (H : Program 1) (M W : Program 2) (entries gamma context : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn entries z))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  obtain ⟨he⟩ := he
  obtain ⟨hz⟩ := EntryFactsConstructorProof.nilAll (body := body) (Delta := Delta) H M W gamma context
  have d := Derivation.equalityElimination
    (EntryFacts.allGood H M W (.var (.inr 0)) (gamma.relabel Sum.inl) (context.relabel Sum.inl))
    (emb z) (emb entries) (symm he)
  simp only [instantiate,bindEmbedding,EntryFactsSyntaxProof.allGoodSubst,liftBind,varBind] at d
  exact ⟨d hz⟩

theorem source (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  have ht := andRight (OriginalTypedDecoderTransportLogicalProof.iffForward
    (OriginalUniverseDecoderTransportLeafAcceptanceProof.nilIff H M W raw types gamma context hc) ha)
  rw [equalEqn] at ht
  have hl := (Continuation20261117.OriginalSignatureStructure.GroundProof.groundListStructure
    body alpha Delta count types hg).1
  have hl0 := headTransport OriginalContextInsertion.length count types z Fin.elim0 ht hl
  have he0 := entriesZero raw entries hc he
  obtain ⟨he0'⟩ := he0
  have hle := headTransport OriginalContextInsertion.length count z entries Fin.elim0 ⟨symm he0'⟩ hl0
  exact andIntro hle (nilGood H M W entries gamma context he0)

theorem target (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (hi : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  have he0 := entriesZero raw entries hc he
  have hl0 := headTransport OriginalContextInsertion.length count entries z Fin.elim0 he0 (andLeft hi)
  have hc0 := OriginalContextInsertionLengthProof.lengthNilRecover count hl0
  have hg0 := headTransport Continuation20261116.OriginalConcreteHeadSignature.groundList types count z Fin.elim0 hc0 hg
  obtain ⟨ht0⟩ := valueUnique Continuation20261116.OriginalConcreteHeadSignature.groundList types z ![z] hg0
    Continuation20261117.OriginalSignatureStructure.GroundSupportProof.zeroValue
  exact headTransport (OriginalUniverseDecoder.argumentsCheck H M W) (suc z) z types ![raw,gamma,context]
    ⟨symm ht0⟩ (AcceptanceConstructorProof.nilAccept H M W raw gamma context hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineNilProof
