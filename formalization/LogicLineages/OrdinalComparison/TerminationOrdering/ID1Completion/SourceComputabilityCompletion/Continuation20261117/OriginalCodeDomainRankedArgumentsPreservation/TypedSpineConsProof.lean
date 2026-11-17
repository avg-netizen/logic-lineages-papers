module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ConsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TypedSpineInvariant TypedSpineInvariantBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw domainType head tail tailCount types tailTypes entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domainType head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types z tailTypes)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry domainType head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList tailTypes tailCount)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W (suc tailCount) entries gamma context)) := by
  have hsmall := andRight (Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof.cons
    raw domainType head tail hc)
  obtain ⟨hrow⟩ := belowRawApply n H M W raw tail tailCount tailTypes tailEntries gamma context ih hsmall
  obtain ⟨hdom⟩ := andIntro hg (andIntro he hgt)
  have hboth : Nonempty (Derivation body Delta
      (((Accepted H M W true tailTypes tail gamma context).imp
        (invariant H M W tailCount tailEntries gamma context)) ⊓
       ((invariant H M W tailCount tailEntries gamma context).imp
        (Accepted H M W true tailTypes tail gamma context)))) :=
    ⟨Derivation.implicationElimination hrow hdom⟩
  have hf := AcceptanceConstructorProof.consForward H M W raw domainType head tail types tailTypes gamma context hc ht ha
  obtain ⟨hs⟩ := andLeft hboth
  obtain ⟨hat⟩ := andRight (andRight hf)
  have hi : Nonempty (Derivation body Delta (invariant H M W tailCount tailEntries gamma context)) :=
    ⟨Derivation.implicationElimination hs hat⟩
  exact andIntro (OriginalContextInsertionLengthProof.lengthCons entries entry tailEntries tailCount hl (andLeft hi))
    (TypedSpineConstructorProof.sourceCons H M W raw domainType head tail types tailTypes entry entries
      tailEntries gamma context hc ht hp hl ha (andRight hi))

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw domainType head tail tailCount types tailTypes entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domainType head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types z tailTypes)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry domainType head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList tailTypes tailCount)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (invariant H M W (suc tailCount) entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  have hsmall := andRight (Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof.cons
    raw domainType head tail hc)
  obtain ⟨hrow⟩ := belowRawApply n H M W raw tail tailCount tailTypes tailEntries gamma context ih hsmall
  obtain ⟨hdom⟩ := andIntro hg (andIntro he hgt)
  have hboth : Nonempty (Derivation body Delta
      (((Accepted H M W true tailTypes tail gamma context).imp
        (invariant H M W tailCount tailEntries gamma context)) ⊓
       ((invariant H M W tailCount tailEntries gamma context).imp
        (Accepted H M W true tailTypes tail gamma context)))) :=
    ⟨Derivation.implicationElimination hrow hdom⟩
  have hi := andIntro (ConsLengthProof.tailLength entries entry tailEntries tailCount hl (andLeft ha))
    (EntryFactsHeadProof.tailAll H M W entries entry tailEntries gamma context hl (andRight ha))
  obtain ⟨hs⟩ := andRight hboth
  obtain ⟨hi⟩ := hi
  have hat : Nonempty (Derivation body Delta (Accepted H M W true tailTypes tail gamma context)) :=
    ⟨Derivation.implicationElimination hs hi⟩
  exact TypedSpineConstructorProof.targetCons H M W raw domainType head tail types tailTypes entry entries
    tailEntries gamma context hc ht hp hl (andRight ha) hat
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsProof
