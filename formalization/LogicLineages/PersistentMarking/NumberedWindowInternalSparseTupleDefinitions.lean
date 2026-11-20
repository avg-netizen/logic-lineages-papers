module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuple
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (someAddressPositive)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
  (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparsePathAdvanceTargets
  (ActualRawCalibration ActualLeastCalibration ActualAdvanceCalibration)
open NumberedWindowInternalSparsePositiveFoldTargets
  (ActualFuelCalibration ActualPositiveCalibration)

/-- These are the actual numeric callees of the installed AST, not
interface assumptions asserted as object-language implications. -/
def CallbacksAt (xs : Entries) (s : Settings) (cv tv : Program 1)
    (raw : Program 5) (least : Program 3) : Prop :=
  ActualContextGuard cv ∧ ActualTypeGuard tv ∧
  ActualRawCalibration xs s raw ∧ ActualLeastCalibration s least ∧
  ActualAdvanceCalibration xs s raw least ∧ ActualFuelCalibration xs s raw least ∧
  ActualPositiveCalibration xs s raw least

/-- The same `accepts` expression used by original matching, with
certificate in its middle slot, inside the actual newly installed
source body. The raw four-field report belongs to that physical r. -/
def InstalledReportAt (i j cv tv : Program 1) (d : Program 3)
    (raw : Program 5) (least : Program 3) : Prop :=
  let r := addressPositive cv tv raw least
  ∀ (c : Nat) (α : Type) (left cert right : OTerm α),
    let accepted := accepts r left cert right
    let reported := someAddressPositive cv tv raw least left cert right
    Nonempty (Derivation (sourceBody (data i j r d) c) []
      ((accepted.imp reported) ⊓ (reported.imp accepted)))

/-- Literal existing TupleAt interface; its original i/j/d, guarded p,
v, chosen A/H, typing, and given-fresh alignment are reinstantiated
on this body. All coordinate programs remain individually available. -/
def InstalledTupleAt (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j cv tv : Program 1) (d p₀ : Program 3)
    (raw : Program 5) (least : Program 3) (v : Inputs) : Prop :=
  TupleAt xs s W i j (addressPositive cv tv raw least) d v ∧
  v.applicationGuard = guard i p₀ ∧
  CallbacksAt xs s cv tv raw least ∧
  InstalledReportAt i j cv tv d raw least

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuple
