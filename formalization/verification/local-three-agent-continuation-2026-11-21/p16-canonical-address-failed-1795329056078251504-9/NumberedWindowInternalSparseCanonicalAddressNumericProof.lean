module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSideProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorThree)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run applyUnary)
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof (acceptedBoth sideReports)
open NumberedWindowInternalSparseAddressPositiveNumericShapeProof (Decoded decodedView viewDecoded unpackContext)
open NumberedWindowInternalSparseAddressPositiveNumericSideProof (fields reportsOf decodedOf)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparseCanonicalCoordinatesChecks (exact_CoordinateCalibration)
open NumberedWindowInternalSparseCanonicalCoordinatesTargets (canonicalCoordinates)
open NumberedWindowScalarAlgorithm (scalar canonical)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowInternalSparseCanonicalAddressTargets

private theorem shape (cv tv : Program 1) (q : Nat) :
    run (shapeChecks cv tv) q = 1 ↔ sideReports cv tv q := by
  change evaluate (shapeChecks cv tv) (q ::ᵥ nil) = 1 ↔ _
  simp only [shapeChecks,acceptedBoth,sideReports]
  change _ ∧ (run (applyUnary cv rawContext) q = 1 ∧ run (applyUnary tv rawResult) q = 1) ↔ _
  rw [applyValue,applyValue]
  rfl

private theorem call (W least : Program 3) (q : Nat) :
    run (coordinateCall W least) q = evaluate (canonicalCoordinates W least)
      (run rawContext q ::ᵥ run rawResult q ::ᵥ run rawLeast q ::ᵥ nil) := by
  change evaluate (canonicalCoordinates W least) (List.Vector.ofFn (fun i : Fin 3 =>
    run ((![rawContext,rawResult,rawLeast] : Fin 3 → Program 1) i) q)) = _
  rw [vectorThree]
  rfl

theorem calibration : ExactAddressScalarCalibration := by
  intro s cv tv W least hc ht hw hl q
  rw [addressScalar,actualConjunctionEvaluation]
  change (if run (shapeChecks cv tv) q = 1 ∧ run (coordinateCall W least) q = 1 then 1 else 0) = _
  simp only [shape,call,exact_CoordinateCalibration s W least hw hl]
  cases view : addressView q with
  | none =>
    have bad : ¬ sideReports cv tv q := by
      intro side
      obtain ⟨d⟩ := decodedOf hc ht side
      have valid := decodedView d
      rw [view] at valid
      contradiction
    simp [bad,scalar,view]
  | some v =>
    rcases v with ⟨g,t,k⟩
    obtain ⟨d,hg,hty,hk⟩ := viewDecoded view
    have side := reportsOf hc ht d
    obtain ⟨c,u,r⟩ := fields d
    rw [c,u,r,unpackContext d.contextOk,hg,hty,hk]
    cases he : canonical s (g,t,k) <;> simp [side,he,scalar,view]
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressNumericProof
