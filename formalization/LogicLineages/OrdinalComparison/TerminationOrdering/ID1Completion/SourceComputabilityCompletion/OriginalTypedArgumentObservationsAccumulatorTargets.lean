module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Two arbitrary same-count walks starting at the SAME raw spine and runtime
parameter preserve a literal numeric-list accumulator suffix. Every state,
list, R computation and output is an actual original graph. This is independent
of source validity, native calibration and eventual termination. -/
def AccumulatorSuffix : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha))
 (count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial1 raw acc1)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial2 raw acc2)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)) →
 Nonempty (Derivation body Delta (graph3 (walk R) out1 count initial1 parameter)) →
 Nonempty (Derivation body Delta (graph3 (walk R) out2 count initial2 parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out1 remaining1 result1)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out2 remaining2 result2)) →
 Nonempty (Derivation body Delta (equal remaining1 remaining2 ⊓
   graph2 InternalApplicationValidityStackAppend.append result2 result1 suffix))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorTargets
