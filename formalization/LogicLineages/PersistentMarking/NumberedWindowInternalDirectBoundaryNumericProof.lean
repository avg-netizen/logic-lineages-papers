module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open ID1Completion.InternalListMapEvaluationProof (actualRawListMapEvaluation)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseScratchMembershipNumericProof (allInput)
open NumberedWindowInternalDirectBoundaryGuardsTargets
open NumberedWindowInternalDirectRawSourceNumericProof (exact_OriginalRawSourceCheckNumeric)

private theorem normalization (scalar : Program 1) (test : Nat → Bool)
    (fit : ScalarFit scalar test) (x : Nat) :
    evaluate (normalizeScalar scalar) (x ::ᵥ nil) = (test x).toNat := by
  unfold normalizeScalar
  rw [conjunctionEvaluation,fit x]
  change (if (test x).toNat = 1 ∧ (1 : Nat) = 1 then 1 else 0) = (test x).toNat
  cases test x <;> decide

private theorem mismatch (test : Nat → Bool) (xs : List Nat) :
    (xs.map (fun x => (test x).toNat)).any (fun v => v == 0) = !(xs.all test) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.any_cons,List.all_cons,ih]
    cases test x <;> cases xs.all test <;> decide

theorem exact_TypedScratchNumeric (scalar : Program 1) (test : Nat → Bool) (fit : ScalarFit scalar test)
    (xs : List Nat) : evaluate (typedScratch scalar) (numbersNumber xs ::ᵥ nil) = (xs.all test).toNat := by
  have mapped : evaluate (ID1Completion.InternalListMap.map (k := 0) (normalizeScalar scalar))
      (numbersNumber xs ::ᵥ nil) = numbersNumber (xs.map (fun x => (test x).toNat)) := by
    rw [actualRawListMapEvaluation,numbersRoundTrip]
    simp only [Option.getD,normalization scalar test fit]
  have rejected : evaluate (scalarFailures scalar) (numbersNumber xs ::ᵥ nil) = (!(xs.all test)).toNat := by
    unfold scalarFailures
    rw [evaluate,vectorTwo]
    change evaluate NumberedWindowInternalSparseScratchMembership.scratchMember
      (evaluate (ID1Completion.InternalListMap.map (k := 0) (normalizeScalar scalar))
        (numbersNumber xs ::ᵥ nil) ::ᵥ 0 ::ᵥ nil) = _
    rw [mapped,allInput,numbersRoundTrip]
    change ((xs.map (fun x => (test x).toNat)).any (fun v => v == 0)).toNat = _
    rw [mismatch]
  unfold typedScratch
  rw [evalBranch,rejected]
  change (if (!(xs.all test)).toNat = 0 then 1 else 0) = (xs.all test).toNat
  cases xs.all test <;> decide

private theorem presence (xs : List Nat) :
    evaluate presentScratch (numbersNumber xs ::ᵥ nil) = (!xs.isEmpty).toNat := by
  unfold presentScratch
  rw [evalBranch]
  change (if numbersNumber xs = 0 then 0 else 1) = _
  cases xs <;> simp [numbersNumber,Bool.toNat]

private theorem atSlotValue (p : Program 1) (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (atSlot p i) xs = evaluate p (xs.get i ::ᵥ nil) := by
  unfold atSlot
  rw [evaluate,vectorOne]
  rfl

private theorem guardBit {n : Nat} (p q : Program n) (tape : List.Vector Nat n) (x y : Bool)
    (a : evaluate p tape = x.toNat) (b : evaluate q tape = y.toNat) :
    evaluate (ID1Completion.InternalAcceptance.conjunction p q) tape = (x && y).toNat := by
  rw [conjunctionEvaluation,a,b]
  cases x <;> cases y <;> rfl

theorem exact_BoundaryScratchNumeric (scalar : Program 1) (test : Nat → Bool)
    (fit : ScalarFit scalar test) (xs ys rs : List Nat) :
    evaluate (boundaryScratch scalar) (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber rs ::ᵥ nil)
      = (xs.all test && ys.all test && !rs.isEmpty).toNat := by
  let tape := numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber rs ::ᵥ nil
  have left := (atSlotValue (typedScratch scalar) 0 tape).trans (exact_TypedScratchNumeric scalar test fit xs)
  have right := (atSlotValue (typedScratch scalar) 1 tape).trans (exact_TypedScratchNumeric scalar test fit ys)
  have rem := (atSlotValue presentScratch 2 tape).trans (presence rs)
  have h := guardBit (atSlot (typedScratch scalar) 1) (atSlot presentScratch 2) tape
    (ys.all test) (!rs.isEmpty) right rem
  simpa only [boundaryScratch,Bool.and_assoc] using
    guardBit (atSlot (typedScratch scalar) 0) _ tape (xs.all test) _ left h

theorem exact_DirectBoundaryRawNumeric : ExactNumericRawGuards := by
  intro scalar test fit src dst removed
  unfold boundaryRaw expected
  rw [exact_OriginalRawSourceCheckNumeric]
  cases unpack src <;> cases unpack dst <;> cases unpack removed <;> try rfl
  rename_i xs ys rs
  change (if evaluate (boundaryScratch scalar)
      (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber rs ::ᵥ nil) = 1 then 1 else 0) =
    (xs.all test && ys.all test && !rs.isEmpty).toNat
  rw [exact_BoundaryScratchNumeric scalar test fit]
  cases (xs.all test && ys.all test && !rs.isEmpty) <;> rfl

#print axioms exact_TypedScratchNumeric
#print axioms exact_BoundaryScratchNumeric
#print axioms exact_DirectBoundaryRawNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryNumericProof
