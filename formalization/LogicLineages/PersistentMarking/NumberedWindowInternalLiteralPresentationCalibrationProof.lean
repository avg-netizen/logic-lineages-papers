module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
public import LogicLineages.PersistentMarking.NumberedWindowPresentationCheckers
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPresentationCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowDirectAlgorithm (typedList)
open NumberedWindowInternalDirectTypedListTargets (ExactNumericJRaw jRaw typedPayload parsedPayload)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit typedScratch)
open NumberedWindowInternalDirectBoundaryNumericProof (exact_TypedScratchNumeric)
open NumberedWindowInternalFunctionalRawUnionNumericProof (exact_ParsedPayloadOnList)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualAddressPositiveCalibration)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectCoreCalibrationProof (exact_OriginalDirectCoreNumeric)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)

/-- The same J-carrier used in the installed literal body rejects genuinely
malformed raw fields, accepts the empty list, and checks every selected
scalar on successful lists without changing their order or multiplicity. -/
theorem exact_OriginalJRawNumeric : ExactNumericJRaw := by
  intro i test fit raw
  unfold jRaw typedList
  rw [evalBranch,exact_ActualEncodedOutput]
  cases h : unpack raw with
  | none => rfl
  | some xs =>
    change (if numbersNumber xs + 1 = 0 then 0 else evaluate (typedPayload i) (raw ::ᵥ nil)) =
      (xs.all test).toNat
    rw [if_neg (Nat.succ_ne_zero _)]
    unfold typedPayload
    rw [evaluate,vectorOne]
    change evaluate (typedScratch i) (evaluate parsedPayload (raw ::ᵥ nil) ::ᵥ nil) = _
    rw [exact_ParsedPayloadOnList raw xs h]
    exact exact_TypedScratchNumeric i test fit xs

/-- Both visibly installed multiset programs compute the original exact
Paper 16 checks, for every raw input, as soon as the scalar and positive
programs do. No extensional substitution of proof trees is used. -/
theorem exact_LiteralWindowCalibration (xs : Entries) (s : Settings) (i : Program 1) (r : Program 3)
    (scalarFit : ScalarFit i (scalar s))
    (positiveFit : NumberedWindowInternalDirectCoreNumericTargets.PositiveFit r
      (NumberedWindowConcreteCheckers.positive xs s)) :
    Evaluates (checks xs s) i (jRaw i) r (dCore i r permutation) ∧
      Interprets (checks xs s) (literalData i r) := by
  have vals : Evaluates (checks xs s) i (jRaw i) r (dCore i r permutation) := by
    refine ⟨scalarFit,exact_OriginalJRawNumeric i (scalar s) scalarFit,positiveFit,?_⟩
    exact exact_OriginalDirectCoreNumeric i r permutation (scalar s)
      (NumberedWindowConcreteCheckers.positive xs s) scalarFit positiveFit exact_OriginalLiteralCountFit
  exact ⟨vals,NumberedWindowFormulaCalibrationChecks.exact_InterpretsEvaluatingPrograms
    (checks xs s) i (jRaw i) r (dCore i r permutation) vals⟩

/-- Instantiate the exact joint literal body at the same physically
selected address-positive program. This offers a direct installation
route, not an assertion about any older derivation on a different body. -/
theorem exact_SelectedLiteralWindowCalibration (xs : Entries) (s : Settings)
    (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (scalarFit : ScalarFit i (scalar s))
    (positiveFit : ActualAddressPositiveCalibration xs s cv tv raw least) :
    let r := addressPositive cv tv raw least
    Evaluates (checks xs s) i (jRaw i) r (dCore i r permutation) ∧
      Interprets (checks xs s) (literalData i r) :=
  exact_LiteralWindowCalibration xs s i (addressPositive cv tv raw least) scalarFit positiveFit

#print axioms exact_OriginalJRawNumeric
#print axioms exact_LiteralWindowCalibration
#print axioms exact_SelectedLiteralWindowCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPresentationCalibrationProof
