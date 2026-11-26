module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply cancelSuc symm)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransport
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tailPositive (raw typ head tail entries tailValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail z))) :
    Nonempty (Derivation body Delta (eqn tailValue z).not) := by
  have hz : Nonempty (Derivation body (eqn tailValue z :: Delta) (eqn tailValue z)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht0 := outputTransport ArgumentEntriesRecursor.extract tailValue z ![tail,z] hz (withHyp ht _)
  have hfail := StandaloneConsExtraction.Proof.consFailure body alpha _ raw typ head tail z (withHyp hc _) ht0
  obtain ⟨hbad⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) z ![raw,z] (withHyp he _) hfail
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hbad)⟩

theorem entriesCons (raw typ head tail entries tailEntries entry listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)) := by
  have hx := StandaloneConsExtraction.Proof.consSuccess body alpha Delta raw typ head tail z tailEntries entry listCode hc ht hp hl
  obtain ⟨heq⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) (suc listCode) ![raw,z] he hx
  exact outputTransport InternalListCodec.consCode listCode entries ![entry,tailEntries] ⟨symm (cancelSuc heq)⟩ hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsSupportProof
