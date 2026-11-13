module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- A genuine singleton term return is executed at every positive fuel. The
entire final state, including results, is the actual unchanged return Program's
output. No completed-state or result-stack invariant is a premise. -/
def PositiveReturnState : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame payload extra output : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc extra) input)) →
 Nonempty (Derivation body Delta
   (OriginalHereditaryPotentialCompletion.Empty output ⊓
    graph1 (OriginalHereditaryReturnStep.step R) output input))
/-- The first coordinate of the actual final result at every positive return
fuel is the original root observation. Input results and stored counters remain
arbitrary. This does not presume that a source-root run reached this agenda. -/
def PositiveReturnProjection : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame payload packed parameter extra output outWork stack value old root tail : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc extra) input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnTargets
