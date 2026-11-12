module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Literal encoded return-frame geometry. No derived selector graph is assumed;
the frame tag and role remain arbitrary until a return rule chooses them. -/
def ActualCoordinates : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest tag payload parent counts role typed rawJob typ raw parameter children deletions packed : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame tag payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta
  (graph1 OriginalHereditaryReturnStep.role role input ⊓
   graph1 OriginalHereditaryReturnStep.expectedType typ input ⊓
   graph1 OriginalHereditaryReturnStep.raw raw input ⊓
   graph1 OriginalHereditaryReturnStep.parameter parameter input ⊓
   graph1 OriginalHereditaryReturnStep.childCount children input ⊓
   graph1 OriginalHereditaryReturnStep.deletionCount deletions input ⊓
   graph1 OriginalHereditaryReturnStep.packed packed input ⊓
   graph1 OriginalHereditaryReturnStep.results results input))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesTargets
