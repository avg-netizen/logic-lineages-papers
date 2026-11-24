module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowRawExchangeSymmetryChecks (exact_RawExchangeSymmetry)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated factoredCover)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredExchangeThinNumericProof (exact_LiteralMeasuredExchangeCalibration)

def swapExchange (X : Program 2) : Program 2 := .composition X ![.projection 1,.projection 0]
def pairedExchange (X : Program 2) : Program 2 := conjunction X (swapExchange X)

theorem exact_LiteralPairedCalibration (s : Settings) (X : Program 2)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (hX : ActualTermExchange s X) :
    ActualTermExchange s (pairedExchange X) := by
  intro a b
  let xs := List.Vector.ofFn (exchangeTape a b)
  have rev : evaluate (swapExchange X) xs = evaluate X (List.Vector.ofFn (exchangeTape b a)) := by
    change evaluate X (List.Vector.ofFn (fun i : Fin 2 =>
      evaluate ((![.projection 1,.projection 0] : Fin 2 → Program 2) i) xs)) = _
    rw [vectorTwo,vectorTwo]
    rfl
  have same := exact_RawExchangeSymmetry s.equivalentHeads symmetric a b
  change evaluate (pairedExchange X) xs = _
  rw [pairedExchange,actualConjunctionEvaluation,rev,hX b a,← same]
  have fwd : evaluate X xs = ((bits s.equivalentHeads a b).1).toNat := hX a b
  rw [fwd]
  cases (bits s.equivalentHeads a b).1 <;> rfl

/-- Original intrinsic directed/paired/guarded wiring, with original
guardedExchange itself (its arithmetic numerical root is already thin). -/
def measuredFactoredExchange (s : Settings) (base : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) : Program 2 :=
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  guardedExchange C s (pairedExchange (measuredExchange M (selected (step base V))))

theorem exact_LiteralMeasuredFactoredCalibration (s : Settings) (base : Program 2)
    (V baseM : Program 1) (P : Program 2) (G : Program 3)
    (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (cover : ActualSelectedCoverOutput (factoredCover V (selectedMeasure (measureUpdate baseM P)) G))
    (measure : TermMeasureCalibrated (selectedMeasure (measureUpdate baseM P)))
    (directed : ActualTermExchange s (selected (step base V))) :
    ActualTermExchange s (measuredFactoredExchange s base V baseM P G) := by
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  let D := selected (step base V)
  have measured : ActualTermExchange s (measuredExchange M D) :=
    exact_LiteralMeasuredExchangeCalibration s M D measure directed
  have paired : ActualTermExchange s (pairedExchange (measuredExchange M D)) :=
    exact_LiteralPairedCalibration s (measuredExchange M D) symmetric measured
  exact NumberedWindowInternalSparseCoverGuardedExchangeNumericProof.calibration
    C s (pairedExchange (measuredExchange M D)) cover paired

#print axioms exact_LiteralPairedCalibration
#print axioms exact_LiteralMeasuredFactoredCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
