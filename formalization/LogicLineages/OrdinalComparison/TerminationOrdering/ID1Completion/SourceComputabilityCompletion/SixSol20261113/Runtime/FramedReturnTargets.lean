module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- One literal return tick over an arbitrary agenda suffix. No assumption
on result correctness, termination, or empty agenda is supplied. -/
def ActualFramedReturnState : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame suffix payload output : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc (numeral 0)) input)) →
 Nonempty (Derivation body Delta
   (graph1 InternalUnpair.left suffix output ⊓
    graph1 (OriginalHereditaryReturnStep.step R) output input))

/-- Full term-return content at the same single tick, with arbitrary background. -/
def ActualFramedReturnContent : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame suffix payload packed parameter first second output outWork stack value old root tail returned row : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.firstSlot first input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.secondSlot second input)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc (numeral 0)) input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)) →
 Nonempty (Derivation body Delta
   (graph2 (OriginalRootObservation.rootObservation R) root packed parameter ⊓
    (graph3 OriginalHereditaryReturn.returnRoot returned packed first second ⊓
     (graph1 OriginalHereditaryReturnStep.deletionRow row input ⊓
      graph1 OriginalHereditaryReturnStep.oldSuffix old input))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnTargets
