module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsHeadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.AcceptanceConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EntryFacts
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sourceCons (H : Program 1) (M W : Program 2)
    (raw domain head tail types tailTypes entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types z tailTypes)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry domain head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)))
    (hi : Nonempty (Derivation body Delta (allGood H M W tailEntries gamma context))) :
    Nonempty (Derivation body Delta (allGood H M W entries gamma context)) := by
  have h := AcceptanceConstructorProof.consForward H M W raw domain head tail types tailTypes gamma context hc ht ha
  have he := (EntryCheckProof.entryIff H M W entry domain head gamma context hp).mpr
    ⟨andLeft h,andLeft (andRight h)⟩
  exact EntryFactsConstructorProof.consAll H M W entries entry tailEntries gamma context hl he hi

theorem targetCons (H : Program 1) (M W : Program 2)
    (raw domain head tail types tailTypes entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types z tailTypes)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry domain head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (ha : Nonempty (Derivation body Delta (allGood H M W entries gamma context)))
    (hi : Nonempty (Derivation body Delta (Accepted H M W true tailTypes tail gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  have hh := EntryFactsHeadProof.headAccepted H M W entries entry tailEntries gamma context hl ha
  obtain ⟨he,hh⟩ := (EntryCheckProof.entryIff H M W entry domain head gamma context hp).mp hh
  exact AcceptanceConstructorProof.consBackward H M W raw domain head tail types tailTypes gamma context
    hc ht he hh hi
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConstructorProof
