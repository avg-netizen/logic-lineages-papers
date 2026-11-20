module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (contextView typeBit)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathAdvanceTargets
  (ActualRawCalibration ActualLeastCalibration ActualAdvanceCalibration)
open NumberedWindowInternalSparsePositiveFoldTargets
  (ActualFuelCalibration ActualPositiveCalibration)
open NumberedWindowInternalSparseAddressPositive (addressPositive)

def ActualContextGuard (p : Program 1) : Prop :=
  ∀ n, evaluate p (n ::ᵥ nil) = (contextView n).isSome.toNat

def ActualTypeGuard (p : Program 1) : Prop :=
  ∀ n, evaluate p (n ::ᵥ nil) = (typeBit n).toNat

def ActualAddressPositiveCalibration (entries : Entries) (s : Settings)
    (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3) : Prop :=
  ∀ source cert target,
    evaluate (addressPositive ctxValid tyValid raw least)
      (source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
        (NumberedWindowConcreteCheckers.positive entries s source cert target).toNat

/-- Calibration is the original complete checker even at malformed raw
addresses, contexts, types, and witness codes; not an admitted-input
agreement. The actual selected same-fiber core remains unmodified. -/
def AddressPositiveComposition : Prop :=
  ∀ (entries : Entries) (s : Settings) (ctxValid tyValid : Program 1)
    (raw : Program 5) (least : Program 3),
    ActualContextGuard ctxValid → ActualTypeGuard tyValid →
    ActualPositiveCalibration entries s raw least →
    ActualAddressPositiveCalibration entries s ctxValid tyValid raw least

/-- Genuine executable choices exist together for both validation
programs and the same actual raw/least/advance/fuel/positive chain.
No caller-supplied numeral checker or semantic oracle is presumed. -/
def ConcreteAddressPositive : Prop :=
  ∀ (entries : Entries) (s : Settings),
    ∃ (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3),
      ActualContextGuard ctxValid ∧ ActualTypeGuard tyValid ∧
      ActualRawCalibration entries s raw ∧ ActualLeastCalibration s least ∧
      ActualAdvanceCalibration entries s raw least ∧
      ActualFuelCalibration entries s raw least ∧ ActualPositiveCalibration entries s raw least ∧
      ActualAddressPositiveCalibration entries s ctxValid tyValid raw least

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
