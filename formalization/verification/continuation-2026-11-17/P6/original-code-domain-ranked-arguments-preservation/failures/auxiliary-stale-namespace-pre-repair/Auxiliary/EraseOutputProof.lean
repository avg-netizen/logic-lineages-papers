module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseResultTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open EraseInvariant
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem transfer (raw needle acc bit rest actual actualBit actualRest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual raw needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual actualBit actualRest)))
    (h : Nonempty (Derivation body Delta (result raw needle bit rest))) :
    Nonempty (Derivation body Delta (result raw needle actualBit actualRest)) := by
  have he := valueUnique Erase.state acc actual ![raw,needle] hv ha
  have hpa := outputTransport InternalPairing.pairing acc actual ![bit,rest] he hp
  have hb := valueUnique InternalUnpair.left bit actualBit ![actual]
    (pairLeft actual bit rest hpa) (pairLeft actual actualBit actualRest hap)
  have hr := valueUnique InternalUnpair.right rest actualRest ![actual]
    (pairRight actual bit rest hpa) (pairRight actual actualBit actualRest hap)
  exact EraseResultTransportProof.restTransport raw needle actualBit rest actualRest hr
    (EraseResultTransportProof.bitTransport raw needle bit actualBit rest hb h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseOutputProof
