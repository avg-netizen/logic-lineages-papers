module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open UniformCertificateCompletion OriginalPositionStructuralKeyOpeningDefinitions

/-- Finite actual constructor interface for the paired cutoff observation.
All six source graphs and four child type graphs are explicit. These are
ordinary original decoder/constructor premises, not key covariance or a
class hit. A later Indexed.ApplicationLaw must derive this interface from
its own selected traversal. No full-fold or canonical claim is made here. -/
def ActualApplication : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input out domain codomain arrow fn arg fnOut argOut parameter cutoff fMark aMark mark : OTerm alpha),
 let O := OriginalClassContextAllPositionObserver.positionObservation
   (OriginalStructuralClassKeyDefinitions.key p H G W)
 Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)) →
 Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) fn parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) arg parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) fnOut parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) argOut parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain codomain)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fnOut)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain arg)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain argOut)) →
 Nonempty (Derivation body Delta (graph4 application input domain codomain fn arg)) →
 Nonempty (Derivation body Delta (graph4 application out domain codomain fnOut argOut)) →
 Nonempty (Derivation body Delta (graph3 O fMark cutoff fn parameter)) →
 Nonempty (Derivation body Delta (graph3 O fMark cutoff fnOut parameter)) →
 Nonempty (Derivation body Delta (graph3 O aMark cutoff arg parameter)) →
 Nonempty (Derivation body Delta (graph3 O aMark cutoff argOut parameter)) →
 Nonempty (Derivation body Delta
   ((graph3 O mark cutoff out parameter).iff (graph3 O mark cutoff input parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationTargets
