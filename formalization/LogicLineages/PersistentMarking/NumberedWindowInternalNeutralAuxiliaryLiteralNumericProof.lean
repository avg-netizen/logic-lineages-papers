module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryNumericCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsScalarProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (neutralWithCarrier)
open NumberedWindowInternalNeutralAuxiliaryRefinement (neutralPositive)
open NumberedWindowInternalNeutralAuxiliaryNumericCalibrationProof (exact_OriginalNeutralPositive)
open NumberedWindowConcretePositiveEndpointsScalarProof (scalarEndpoints)
open NumberedWindowInternalAtomicRefinement (atTarget refined)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (targetValue)
open NumberedWindowInternalAtomicRefinementNumericChecks (exact_OriginalPositiveRefinement)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalAuxBottomRefinementNumericChecks (exact_OriginalAuxBottomRefinement)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowCopyAlgorithm (Entries)

theorem exact_NeutralWithCarrierNumeric (xs : Entries) (s : Settings) (i : Program 1)
    (r : Program 3) (scalarCal : ∀ y, run i y = (scalar s y).toNat)
    (old : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) :
    ∀ x w y, evaluate (neutralWithCarrier i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      (positive xs s x w y).toNat := by
  intro x w y
  change evaluate (conjunction (neutralPositive i r) (atTarget i)) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = _
  rw [actualConjunctionEvaluation,exact_OriginalNeutralPositive xs s i r scalarCal old,
    targetValue,scalarCal]
  cases h : positive xs s x w y with
  | false => simp
  | true =>
    have carrier := (scalarEndpoints xs s x w y h).2
    simp [carrier]

/-- This is the actual nested even leaf of literalNeutral, not a new
extensionally equal checker selected in its place. -/
theorem exact_LiteralNeutralEvenNumeric (xs : Entries) (s : Settings) (i : Program 1)
    (r : Program 3) (scalarCal : ∀ y, run i y = (scalar s y).toNat)
    (old : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) :
    ∀ x w y, evaluate (augmented i (neutralWithCarrier i r)) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      (positive xs s x w y).toNat :=
  exact_OriginalAuxBottomRefinement xs s i (refined i (neutralWithCarrier i r)) scalarCal
    (exact_OriginalPositiveRefinement xs s i (neutralWithCarrier i r) scalarCal
      (exact_NeutralWithCarrierNumeric xs s i r scalarCal old))

#print axioms exact_NeutralWithCarrierNumeric
#print axioms exact_LiteralNeutralEvenNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralNumericProof
