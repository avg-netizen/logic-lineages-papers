module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceResultProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EraseAbsence

theorem transfer (raw needle acc bit rest actual actualBit actualRest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual raw needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual actualBit actualRest)))
    (h : Nonempty (Derivation body Delta (result raw needle bit))) :
    Nonempty (Derivation body Delta (result raw needle actualBit)) := by
  have he := valueUnique Erase.state acc actual ![raw,needle] hv ha
  have hpa := outputTransport InternalPairing.pairing acc actual ![bit,rest] he hp
  have hb := valueUnique InternalUnpair.left bit actualBit ![actual]
    (pairLeft actual bit rest hpa) (pairLeft actual actualBit actualRest hap)
  exact EraseAbsenceResultProof.bitTransport raw needle bit actualBit hb h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceOutputProof
