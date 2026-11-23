module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankEvenOriginalNumericProof
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsScalarProof
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
  (actualConjunctionEvaluation)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowConcretePositiveEndpointsScalarProof (scalarEndpoints)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (targetValue)
open NumberedWindowInternalRankUniversalCarrier
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalKeepsNeutralRank)
open NumberedWindowInternalNeutralRankEvenOriginalNumericProof (exact_OriginalRankEvenAllInputs)

/-- All original settings and all raw tapes. The new requirement does
not exclude any genuinely accepted original edge, including unranked ones. -/
theorem exact_OriginalUniversalEvenCarrierAllInputs (xs : Entries) (s : Settings)
    (i : Program 1) (r : Program 3)
    (iFit : ∀ y, run i y = (scalar s y).toNat)
    (rFit : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) :
    ∀ x w y, evaluate (alwaysCarried i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat := by
  intro x w y
  rw [alwaysCarried,actualConjunctionEvaluation,rFit,targetValue,iFit]
  cases h : positive xs s x w y with
  | false => simp
  | true =>
    have held := (scalarEndpoints xs s x w y h).2
    simp [held]

theorem exact_OriginalCompleteRankEvenAllInputs (xs : Entries) (s : Settings)
    (i raw : Program 1) (r : Program 3)
    (iFit : ∀ y, run i y = (scalar s y).toNat)
    (rawFit : ∀ n, run raw n = rawRank n)
    (rFit : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) :
    ∀ x w y, evaluate (completeRankEven i (addressRank raw) r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      (positive xs s x w y).toNat :=
  exact_OriginalRankEvenAllInputs xs s (exact_OriginalKeepsNeutralRank s) i raw
    (alwaysCarried i r) iFit rawFit (exact_OriginalUniversalEvenCarrierAllInputs xs s i r iFit rFit)

#print axioms exact_OriginalUniversalEvenCarrierAllInputs
#print axioms exact_OriginalCompleteRankEvenAllInputs
end LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierNumericProof
