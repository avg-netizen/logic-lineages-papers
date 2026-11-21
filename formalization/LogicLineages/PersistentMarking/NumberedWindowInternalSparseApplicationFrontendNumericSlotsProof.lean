module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSlotsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open NumberedWindowGuardedGraphTargets (atSlot)
open NumberedWindowInternalFreshProbeParsedEmitter
  (addressGood arrowGood rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalSparseApplicationOutputCore (outputCore)
open NumberedWindowInternalSparseApplicationFrontend
open NumberedWindowInternalSparsePathEnvelope (run)

abbrev tape (f u y : Nat) : List.Vector Nat 3 := f ::ᵥ u ::ᵥ y ::ᵥ nil

private theorem acceptedBoth {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs = 1 ↔ evaluate p xs = 1 ∧ evaluate q xs = 1 := by
  rw [actualConjunctionEvaluation]
  split <;> simp_all

private theorem leftValue (p : Program 1) (f u y : Nat) :
    evaluate (atSlot p 0) (tape f u y) = run p f := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.projection (0 : Fin 3)) (tape f u y)) = _
  rw [vectorOne] <;> rfl

private theorem rightValue (p : Program 1) (f u y : Nat) :
    evaluate (atSlot p 1) (tape f u y) = run p u := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.projection (1 : Fin 3)) (tape f u y)) = _
  rw [vectorOne] <;> rfl

private theorem compareSlots (p q : Program 1) (f u y : Nat) :
    evaluate (.composition equalityTest (![atSlot p 0,atSlot q 1] : Fin 2 → Program 3))
      (tape f u y) = 1 ↔ run p f = run q u := by
  change evaluate equalityTest (List.Vector.ofFn fun b : Fin 2 =>
    evaluate ((![atSlot p 0,atSlot q 1] : Fin 2 → Program 3) b) (tape f u y)) = 1 ↔ _
  rw [vectorTwo]
  change evaluate equalityTest (evaluate (atSlot p 0) (tape f u y) ::ᵥ
    evaluate (atSlot q 1) (tape f u y) ::ᵥ nil) = 1 ↔ _
  rw [leftValue,rightValue,exactEqualityEvaluation]
  split <;> simp_all

private theorem vectorSix (v : Fin 6 → Nat) :
    List.Vector.ofFn v = v 0 ::ᵥ v 1 ::ᵥ v 2 ::ᵥ v 3 ::ᵥ v 4 ::ᵥ v 5 ::ᵥ nil := by
  apply List.Vector.ext
  intro k
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_
    (fun c => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => ?_) d) c) b) a) k
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · obtain rfl := Fin.eq_zero e
    simp <;> rfl

private theorem outputValue (least : Program 3) (f u y : Nat) :
    evaluate (callOutput least) (tape f u y) =
      evaluate (outputCore least) (run rawContext f ::ᵥ run rawDomain f ::ᵥ run rawCodomain f ::ᵥ
        run rawLeast f ::ᵥ run rawLeast u ::ᵥ y ::ᵥ nil) := by
  let args : Fin 6 → Program 3 := ![atSlot rawContext 0,atSlot rawDomain 0,atSlot rawCodomain 0,
    atSlot rawLeast 0,atSlot rawLeast 1,.projection 2]
  change evaluate (outputCore least) (List.Vector.ofFn fun b : Fin 6 => evaluate (args b) (tape f u y)) = _
  rw [vectorSix]
  change evaluate (outputCore least) (evaluate (atSlot rawContext 0) (tape f u y) ::ᵥ
    evaluate (atSlot rawDomain 0) (tape f u y) ::ᵥ evaluate (atSlot rawCodomain 0) (tape f u y) ::ᵥ
    evaluate (atSlot rawLeast 0) (tape f u y) ::ᵥ evaluate (atSlot rawLeast 1) (tape f u y) ::ᵥ y ::ᵥ nil) = _
  simp only [leftValue,rightValue]

theorem coreAtOne (least : Program 3) (f u y : Nat) :
    evaluate (applicationCore least) (tape f u y) = 1 ↔
      run addressGood f = 1 ∧ (run addressGood u = 1 ∧ (run arrowGood f = 1 ∧
        (run rawContext f = run rawContext u ∧ (run rawDomain f = run rawResult u ∧
          evaluate (outputCore least)
            (run rawContext f ::ᵥ run rawDomain f ::ᵥ run rawCodomain f ::ᵥ
              run rawLeast f ::ᵥ run rawLeast u ::ᵥ y ::ᵥ nil) = 1)))) := by
  simp only [applicationCore,acceptedBoth,leftValue,rightValue,sameContext,domainAgreement,compareSlots,outputValue]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSlotsProof
