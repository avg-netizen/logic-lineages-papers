module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEvaluatorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal empty-context bottom job, empty old stack, actual computed scheduler
fuel (padding the proved two-step base), and exact returned observation. Pair witnesses only, not a supplied
expansion or transition. This is a base case, not general content correctness. -/
def ActualEvaluator : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw typ packed c parameter rawJob typed job visit work input counts payload frame returnWork middle root tail value stack output fuel : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) (typ))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (typ) (raw))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (c) (z))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob (raw) (parameter))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (typ) (rawJob))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (z) (typed))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (z) (job))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input (work) (z))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts (z) (z))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload (job) (counts))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) (payload))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing middle (returnWork) (z))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail (raw) (z))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value (root) (tail))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output (z) (stack))) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit z)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode returnWork frame z)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value z)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.fuel fuel job)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value packed parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEvaluatorTargets
