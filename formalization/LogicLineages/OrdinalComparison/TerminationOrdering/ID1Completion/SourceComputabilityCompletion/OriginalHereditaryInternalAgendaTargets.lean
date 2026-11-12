module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryInternalAgenda
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Initial : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (H : Program 1) (M W : Program 2)
 (c B parent visit work : OTerm alpha),
 Nonempty (Derivation body Delta (Job H M W c B parent)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) parent)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))) →
 Nonempty (Derivation body Delta (Agenda H M W c B work))
def ReturnPreservation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (H : Program 1) (M W : Program 2)
 (c B work frame rest : OTerm alpha),
 Nonempty (Derivation body Delta (Agenda H M W c B work)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (Agenda H M W c B rest))
def VisitPreservation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (H : Program 1) (M W : Program 2)
 (c B work visit rest parent jobs tagged counts payload returnFrame returnRest next : OTerm alpha),
 Nonempty (Derivation body Delta (Agenda H M W c B work)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode returnRest returnFrame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append next tagged returnRest)) →
 Nonempty (Derivation body Delta (Agenda H M W c B next))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
