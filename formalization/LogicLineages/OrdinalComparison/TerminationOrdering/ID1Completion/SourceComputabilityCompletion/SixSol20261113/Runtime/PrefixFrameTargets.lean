module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ActualIdentity : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)),
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R (numeral 0) (numeral 0) (numeral 0)))
/-- Lift the existing exact job frame without weakening its background
quantifier order. This contract does not assume or prove job admission. -/
def ActualSingleton : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (job count value frame agendaPrefix produced : OTerm alpha),
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) job)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode agendaPrefix frame (numeral 0))) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode produced value (numeral 0))) →
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R agendaPrefix count produced))
/-- Sequential execution preserves both arbitrary backgrounds. Counts add in
execution order and produced rows concatenate in the opposite stack order. -/
def ActualConcatenation : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (first second firstCount secondCount firstRow secondRow agendaPrefix produced : OTerm alpha),
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R first firstCount firstRow)) →
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R second secondCount secondRow)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append agendaPrefix first second)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced secondRow firstRow)) →
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R agendaPrefix (add firstCount secondCount) produced))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameTargets
