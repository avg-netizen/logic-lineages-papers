module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original term-return tick, with arbitrary work and old-result
backgrounds. The forward child observation map is explicitly reversed below
the deletion stack prefix. Original stored role/type/parameter and counters
are retained; slot values and state selectors are recovered internally.
The outer runtime layer uses R, the reconstructed inner observation uses Q.
Neither Q=evaluator R nor recursive correctness is assumed. The deletion field
is identified only as the actual selector, not yet as a semantic deletion row. -/
def ActualTermTick : Prop := ∀ (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced old input work results suffix output outWork stack value outOld root tail returned deletionRow : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
  Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)) →
  Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletionCount gamma)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts childCount deletionCount)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw rawJobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)) →
  Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardChildren childRow)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletionCount deletionPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardChildren)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame suffix)) →
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc z) input)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value outOld)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned deletionRow)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalRootObservation.rootObservation R) root packed parameter ⊓
     (graph2 (OriginalRootObservation.rootObservation Q) returned packed parameter ⊓
      (graph1 OriginalHereditaryReturnStep.deletionRow deletionRow input ⊓
       graph1 OriginalHereditaryReturnStep.oldSuffix outOld input))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentTargets
