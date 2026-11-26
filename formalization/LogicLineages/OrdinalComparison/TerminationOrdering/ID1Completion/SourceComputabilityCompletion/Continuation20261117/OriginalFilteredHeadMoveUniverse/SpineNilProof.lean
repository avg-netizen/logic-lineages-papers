module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsHeadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderTransportLogicalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open SpineInvariant SpineInvariantBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open EntryFactsSyntaxProof
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

theorem source (H : Program 1) (M W : Program 2) (raw entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) :=
  nilGood H M W entries gamma context (entriesZero raw entries hc he)

theorem target (H : Program 1) (M W : Program 2) (raw types gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (ha : Nonempty (Derivation body Delta (Plain H types raw gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  exact iffBackward (OriginalUniverseDecoderTransportLeafAcceptanceProof.nilIff H M W raw types gamma context hc)
    (iffForward (OriginalTypedDecoderTransportLeafAcceptanceProof.nilIff H raw types gamma hc) ha)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineNilProof
