module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Reflection from the literal ordered deletion-row component of one unchanged
hereditary layer. Both actual runtime contexts retain their own length and range
graphs. A shared layer-key output is supplied; erased-key equality is concluded.
No source-class covariance, queried row, row equality or native interpretation
is a premise. The arithmetic positive body stays fixed throughout. -/
def LayerDeletionTransport : Prop :=
  ∀ (R Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter other otherParameter key cutoff gamma count otherGamma otherCount
      erased erasedParameter otherErased otherErasedParameter value otherValue : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryObservationLayer.layer R Q) key input parameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryObservationLayer.layer R Q) key other otherParameter)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.right otherGamma otherParameter)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length otherCount otherGamma)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff otherCount)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedPacked erased cutoff input parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedParameter erasedParameter cutoff input parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedPacked otherErased cutoff other otherParameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedParameter otherErasedParameter cutoff other otherParameter)) →
  Nonempty (Derivation body Delta (graph2 Q value erased erasedParameter)) →
  Nonempty (Derivation body Delta (graph2 Q otherValue otherErased otherErasedParameter)) →
  Nonempty (Derivation body Delta (equal value otherValue))

/-- One finite hereditary layer is consumed by actual context deletion.
The key graphs are exactly family R (depth+1), while the resulting class-key
graphs are exactly family R depth in their genuine deleted runtime contexts.
This does not identify this key with the selected final representative. -/
def FamilyDeletionTransport : Prop :=
  ∀ (R : Program 2) (depth : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter other otherParameter key cutoff gamma count otherGamma otherCount
      erased erasedParameter otherErased otherErasedParameter value otherValue : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryFiniteObserver.family R (depth+1)) key input parameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryFiniteObserver.family R (depth+1)) key other otherParameter)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.right otherGamma otherParameter)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length otherCount otherGamma)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff otherCount)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedPacked erased cutoff input parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedParameter erasedParameter cutoff input parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedPacked otherErased cutoff other otherParameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalClassContextAllPositionObserver.erasedParameter otherErasedParameter cutoff other otherParameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryFiniteObserver.family R depth) value erased erasedParameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryFiniteObserver.family R depth) otherValue otherErased otherErasedParameter)) →
  Nonempty (Derivation body Delta (equal value otherValue))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.Targets
