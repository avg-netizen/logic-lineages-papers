module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSideProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof
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
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (canonicalCoordinates)
open NumberedWindowScalarAlgorithm (scalar canonical)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions

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

/-- Exact all-code calibration of the same physical coordinate test,
without importing the unrelated round-transport theorem. -/
theorem exact_LiteralAddressScalarCalibration : ExactAddressScalarCalibration := by
  intro s cv tv W least hc ht hw hl q
  rw [addressScalar,actualConjunctionEvaluation]
  change (if run (shapeChecks cv tv) q = 1 ∧ run (coordinateCall W least) q = 1 then 1 else 0) = _
  cases view : addressView q with
  | none =>
    have bad : ¬ sideReports cv tv q := by
      intro side
      obtain ⟨d⟩ := decodedOf hc ht side
      have valid := decodedView d
      rw [view] at valid
      contradiction
    have rejected : ¬ (run (shapeChecks cv tv) q = 1 ∧ run (coordinateCall W least) q = 1) :=
      fun h => bad ((shape cv tv q).mp h.1)
    rw [if_neg rejected]
    simp [scalar,view]
  | some v =>
    rcases v with ⟨g,t,k⟩
    obtain ⟨d,hg,hty,hk⟩ := viewDecoded view
    have side := reportsOf hc ht d
    obtain ⟨c,u,r⟩ := fields d
    have valid := (shape cv tv q).mpr side
    have hits := call W least q
    rw [c,u,r,NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof.calibration s W least hw hl,unpackContext d.contextOk,hg,hty,hk] at hits
    cases he : canonical s (g,t,k) with
    | false =>
      have zero : run (coordinateCall W least) q = 0 := by simpa [he] using hits
      rw [if_neg (fun h => Nat.zero_ne_one (zero.symm.trans h.2))]
      simp [scalar,view,he]
    | true =>
      have one : run (coordinateCall W least) q = 1 := by simpa [he] using hits
      rw [if_pos ⟨valid,one⟩]
      simp [scalar,view,he]
#print axioms exact_LiteralAddressScalarCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof
