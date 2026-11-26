module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual bounded-descent PRIOR leaf at the once-minimum selection. Its
original window, original validity and actual range are the only domain
conditions. No intermediate invariant, observer supplier, class hit or native
calibration is a premise. Not the selected OTHER leaf or final traversal. -/
def ActualPreservation : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input parameter mark cutoff : InternalGraphComposition.OTerm alpha),
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let r := OriginalRankGuardedLeaf.refined q H G W
  let D := OriginalRankGuardedLeaf.priorData q H G W
  Nonempty (Derivation body Delta
    ((OriginalIndexedObserverDefinitions.ActualRange cutoff parameter ⊓
      (OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
       (graph2 (InternalOriginalUniformDescentSelection.validity D)
          InternalOriginalStepGuard.one input parameter ⊓
        graph2 (InternalParameterizedCanonicalResultFold.leaf D) out input parameter))).imp
     ((graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        mark cutoff out parameter).iff
      (graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        mark cutoff input parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTargets
