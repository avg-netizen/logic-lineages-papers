module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowAddressAlgorithm (typeBit addressView)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings canonical)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseCanonicalAddressTargets (addressScalar)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets (refittedScalarType)

/-- Every valid type code lies in the window's finite type list. This is the
numeric content of `ActualTypeGuard` for the refitted type checker. It asks a
finite list to contain every code accepted by `typeBit`; no claim is made here
about whether any `Settings` satisfies it. -/
def AllTypesWindowed (s : Settings) : Prop :=
  ∀ n : Nat, typeBit n = true → s.window.1.contains n = true

/-- Every address the original scalar algorithm accepts has its own type in
the window's finite type list. Purely numeric: `addressView` and `canonical`
are the original algorithm's functions, decidable at each address. It is a
condition on `s`, not a consequence of the calibrations; no finite reduction
of the quantifier over addresses is claimed. -/
def AcceptedTypesWindowed (s : Settings) : Prop :=
  ∀ (q : Nat) (ctx : List Nat) (ty k : Nat), addressView q = some (ctx, ty, k) →
    canonical s (ctx, ty, k) = true → s.window.1.contains ty = true

/-- The refitted scalar type checker computes the window type guard
`typeGuard s`, on every natural input, when its two components carry their
accepted calibrations and the window types are grammar types. -/
def ExactRefittedScalarTypeCalibrated : Prop :=
  ∀ (s : Settings) (TV T : Program 1), GrammarTypeInclusion s →
    ActualTypeGuard TV → TypeGuardCalibrated s T →
    TypeGuardCalibrated s (refittedScalarType s TV T)

/-- If the refitted type checker satisfied the accepted `ActualTypeGuard`
calibration, every valid type code would be in the window list. Only the
calibration of `T` is used. -/
def ExactRefittedTypeGuardActualOnlyIf : Prop :=
  ∀ (s : Settings) (TV T : Program 1), TypeGuardCalibrated s T →
    ActualTypeGuard (refittedScalarType s TV T) → AllTypesWindowed s

/-- Under the accepted calibrations the refitted type checker satisfies
`ActualTypeGuard` exactly when every valid type code is in the window list. -/
def ExactRefittedTypeGuardActualIff : Prop :=
  ∀ (s : Settings) (TV T : Program 1), GrammarTypeInclusion s →
    ActualTypeGuard TV → TypeGuardCalibrated s T →
    (ActualTypeGuard (refittedScalarType s TV T) ↔ AllTypesWindowed s)

/-- The accepted installed-tuple predicate, instantiated at the refitted type
checker, forces every valid type code into the window list: its callback
conjunct contains `ActualTypeGuard` of that checker literally. -/
def ExactRefittedInstalledTupleOnlyIf : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy) (i j cv TV T : Program 1)
    (d p₀ : Program 3) (raw : Program 5) (least : Program 3) (v : Inputs),
    TypeGuardCalibrated s T →
    InstalledTupleAt xs s W i j cv (refittedScalarType s TV T) d p₀ raw least v →
    AllTypesWindowed s

/-- The address scalar built with the refitted type checker computes the
original scalar algorithm on every natural input exactly when every accepted
address has a windowed own type. The calibrations of the context guard, of
`TV`, of `T`, of the window and of the least program are the accepted ones. -/
def ExactRefittedAddressScalarCalibrationIff : Prop :=
  ∀ (s : Settings) (cv TV T : Program 1) (W least : Program 3),
    GrammarTypeInclusion s → ActualContextGuard cv → ActualTypeGuard TV →
    TypeGuardCalibrated s T → ActualPackedWindow s W → ActualLeastCalibration s least →
    (ActualScalarCalibration s (addressScalar cv (refittedScalarType s TV T) W least) ↔
      AcceptedTypesWindowed s)

/-- The same equivalence for the scalar of the measured installation whose
type checker is the refitted one. Calibration of that installation's own
window and least programs is a hypothesis here, not a conclusion. -/
def ExactRefittedInstalledScalarCalibrationIff : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3),
    let Q := install s V TV M M0 B T base cv (refittedScalarType s TV T) root other
    GrammarTypeInclusion s → ActualContextGuard cv → ActualTypeGuard TV →
    TypeGuardCalibrated s T → ActualPackedWindow s Q.window →
    ActualLeastCalibration s Q.least →
    (ActualScalarCalibration s Q.scalar ↔ AcceptedTypesWindowed s)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets
