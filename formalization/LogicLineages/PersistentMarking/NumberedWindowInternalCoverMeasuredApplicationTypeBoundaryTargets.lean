module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualTypeGuard)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt refitGuard)
open NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets (refittedScalarType)
open NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets (AllTypesWindowed)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)

/-- Literal ground/arrow codes built using the original numeric arrow constructor.
This is a sequence of natural codes, unrelated to the ordinal tower. -/
def arrowCodeChain : Nat → Nat
  | 0 => 0
  | depth + 1 => arrow 0 (arrowCodeChain depth)

/-- The original course-of-values type test on a literal arrow. This is a
numeric equation, not an inversion rule for derivations of a program graph. -/
def ExactTypeBitArrowLaw : Prop :=
  ∀ dom cod : Nat, typeBit (arrow dom cod) = (typeBit dom && typeBit cod)

/-- An explicit valid code at least as large as each input depth. -/
def ExactValidArrowCodeChain : Prop :=
  ∀ depth : Nat, depth ≤ arrowCodeChain depth ∧ typeBit (arrowCodeChain depth) = true

/-- The actual type checker accepts codes above every numeric bound. -/
def ExactValidTypeCodesUnbounded : Prop :=
  ∀ bound : Nat, ∃ code : Nat, bound < code ∧ typeBit code = true

/-- Every finite numeric list omits a code accepted by the actual type test. -/
def ExactFiniteTypeListOmission : Prop :=
  ∀ codes : List Nat, ∃ code : Nat, typeBit code = true ∧ codes.contains code = false

/-- The finite-window condition exposed by #1464 is impossible for every
Settings value, independently of all program calibrations. -/
def ExactNoAllTypesWindowed : Prop :=
  ∀ s : Settings, ¬ AllTypesWindowed s

/-- The finite grammar list alone forces a genuine valid type to be rejected
by the refit guard and by the refitted scalar type checker. Neither component
program is assumed calibrated. These are evaluation equations on one code. -/
def ExactRefittedValidTypeRejection : Prop :=
  ∀ (s : Settings) (TV T : Program 1), ∃ code : Nat,
    typeBit code = true ∧
    evaluate (grammarTypeAt s) (code ::ᵥ nil) = 0 ∧
    evaluate (refitGuard s T) (code ::ᵥ nil) = 0 ∧
    evaluate (refittedScalarType s TV T) (code ::ᵥ nil) = 0

/-- A numeric counterexample to the type-refit transfer required by the
guard-free route. The actual syntax checker accepts an arrow, its domain and
its codomain, while the refit guard rejects that codomain. This is not a
statement about internal derivability or soundness of an arbitrary body. -/
def ExactActualTypeRefitCounterexample : Prop :=
  ∀ (s : Settings) (TV T : Program 1), ActualTypeGuard TV → ∃ cod : Nat,
    evaluate TV (arrow 0 cod ::ᵥ nil) = 1 ∧
    evaluate TV (0 ::ᵥ nil) = 1 ∧
    evaluate TV (cod ::ᵥ nil) = 1 ∧
    evaluate (refitGuard s T) (cod ::ᵥ nil) = 0

/-- No finite refitted scalar type checker satisfies the actual all-code type
calibration. In particular, no TypeGuardCalibrated premise is needed. -/
def ExactRefittedTypeGuardNeverActual : Prop :=
  ∀ (s : Settings) (TV T : Program 1),
    ¬ ActualTypeGuard (refittedScalarType s TV T)

/-- The accepted installed-tuple predicate contains ActualTypeGuard of its
literal type-checker slot. Thus a refitted checker cannot occupy that slot,
without any assumption on the other programs or on the settings. -/
def ExactRefittedInstalledTupleImpossible : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy) (i j cv TV T : Program 1)
    (d p₀ : Program 3) (raw : Program 5) (least : Program 3) (v : Inputs),
    ¬ InstalledTupleAt xs s W i j cv (refittedScalarType s TV T) d p₀ raw least v

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryTargets
