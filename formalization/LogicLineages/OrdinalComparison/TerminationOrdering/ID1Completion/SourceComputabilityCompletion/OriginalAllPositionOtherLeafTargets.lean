module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The actual selected OTHER leaf, with its real window/source/range and tag.
No prior-leaf preservation, sidecar acceptance or intermediate invariant is
supplied. This is not the full application/lambda traversal. -/
def ActualPreservation : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
   (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (out input parameter mark cutoff : InternalGraphComposition.OTerm alpha),
 let q := OriginalClassContextAllPositionSelection.inputs p H G W P
 let r := OriginalRankGuardedLeaf.refined q H G W
 Nonempty (Derivation body Delta
  ((OriginalIndexedObserverDefinitions.ActualRange cutoff parameter ⊓
   (OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
    (graph2 (InternalOriginalUniformDescentSelection.validity
      (OriginalRankGuardedLeafProof.selectedData q H G W)) InternalOriginalStepGuard.one input parameter ⊓
     (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input ⊓
      graph2 (OriginalLambdaTraversalSelection.leaf r.base r.window) out input parameter)))).imp
   ((graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative) mark cutoff out parameter).iff
    (graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative) mark cutoff input parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTargets
