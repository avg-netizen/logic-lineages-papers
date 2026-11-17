module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedErase

theorem transfer (weight : Program 1) (raw needle acc bit rest actual actualBit actualRest
    total remainingWeight actualWeight needleWeight : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual raw needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual actualBit actualRest)))
    (hw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingWeight rest)))
    (haw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) actualWeight actualRest)))
    (h : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (effect actualBit total actualWeight needleWeight)) := by
  have he := valueUnique Erase.state acc actual ![raw,needle] hv ha
  have hpa := outputTransport InternalPairing.pairing acc actual ![bit,rest] he hp
  have hb := valueUnique InternalUnpair.left bit actualBit ![actual]
    (pairLeft actual bit rest hpa) (pairLeft actual actualBit actualRest hap)
  have hr := valueUnique InternalUnpair.right rest actualRest ![actual]
    (pairRight actual bit rest hpa) (pairRight actual actualBit actualRest hap)
  have hw' := headTransport (Fold.weighted weight) remainingWeight rest actualRest Fin.elim0 hr hw
  have hs := valueUnique (Fold.weighted weight) remainingWeight actualWeight ![actualRest] hw' haw
  exact WeightedEraseTransportProof.remainingWeightTransport actualBit total remainingWeight needleWeight actualWeight hs
    (WeightedEraseTransportProof.bitTransport bit total remainingWeight needleWeight actualBit hb h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseOutputProof
