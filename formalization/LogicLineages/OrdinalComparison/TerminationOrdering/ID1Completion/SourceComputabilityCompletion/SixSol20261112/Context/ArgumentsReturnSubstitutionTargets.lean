module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual argument-cons return reconstruction. The child scalar, tail
argument observation and literal raw cons are actual graphs at the SAME Q
and parameter; no typed numeric observation or desired output cons is a premise. -/
def Cons : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw typ child tail packed first second parameter returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)) →
  Nonempty (Derivation body Delta (graph2 Q first packed parameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) second tail parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons returned raw first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) returned raw parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionTargets
