module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowPositivePathAlgorithm (hopView)
open NumberedWindowInternalSparsePathEnvelope
  (run hopGood hopTarget hopSource hopWitness hopRawTarget selectedHop)
open NumberedWindowInternalSparsePathEnvelopeNumericChecks (exact_AllInputHopEnvelope)
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePathAdvanceEvaluationProof

private theorem successfulCode (x : Option Nat) (n : Nat) :
    encodeState x = n+1 ↔ x = some n := by
  cases x <;> simp [encodeState]

private theorem absentShape {hop : Nat} (bad : hopView hop = none) : run hopGood hop ≠ 1 := by
  intro h
  have eq := exact_AllInputHopEnvelope hop
  simp [selectedHop,h,bad] at eq

private theorem presentShape {hop t q w r : Nat} (found : hopView hop = some (t,q,w,r)) :
    run hopGood hop = 1 ∧ run hopTarget hop = t ∧ run hopSource hop = q ∧
      run hopWitness hop = w ∧ run hopRawTarget hop = r := by
  have eq := exact_AllInputHopEnvelope hop
  by_cases accepted : run hopGood hop = 1
  · refine ⟨accepted,?_⟩
    have same : (run hopTarget hop,run hopSource hop,run hopWitness hop,run hopRawTarget hop) =
        (t,q,w,r) := Option.some.inj (by simpa only [selectedHop,if_pos accepted,found] using eq)
    exact ⟨congrArg Prod.fst same,congrArg (fun x => x.2.1) same,
      congrArg (fun x => x.2.2.1) same,congrArg (fun x => x.2.2.2) same⟩
  · simp [selectedHop,accepted,found] at eq

private theorem passedCalls (entries : Entries) (s : Settings) (raw : Program 5) (p : Program 3)
    (hr : ActualRawCalibration entries s raw) (hp : ActualLeastCalibration s p)
    (c ty current hop target q w r : Nat) (g : List Nat)
    (decoded : unpack c = some g) (found : hopView hop = some (target,q,w,r)) :
    passes raw p c ty (current+1) hop ↔
      NumberedWindowConcreteCheckers.step entries s g ty q w r = true ∧
      least s g ty q = some current ∧ least s g ty r = some target := by
  obtain ⟨good,ht,hq,hw,hr'⟩ := presentShape found
  unfold passes actualStep sourceCode destinationCode
  rw [good,ht,hq,hw,hr',hr c ty q w r,hp c ty q,hp c ty r]
  cases b : NumberedWindowConcreteCheckers.step entries s g ty q w r <;>
    simp [packedRaw,packedLeast,decoded,successfulCode,b]

theorem composition : AdvanceComposition := by
  intro entries s raw p hr hp c ty current hop
  classical
  change eval4 (NumberedWindowInternalSparsePathAdvance.advance raw p) c ty current hop = _
  rw [resultValue]
  cases decoded : unpack c with
  | none =>
    have no : ¬ passes raw p c ty current hop := by
      intro yes
      have bad := yes.2.2.1
      unfold actualStep at bad
      rw [hr c ty (run hopSource hop) (run hopWitness hop) (run hopRawTarget hop)] at bad
      simp [packedRaw,decoded] at bad
    simp [if_neg no,packedOriginalAdvance,decoded,encodeState]
  | some g =>
    cases current with
    | zero =>
      have no : ¬ passes raw p c ty 0 hop := fun h => h.1 rfl
      simp [if_neg no,packedOriginalAdvance,decoded,decodeState,
        NumberedWindowPositivePathAlgorithm.advance,encodeState]
    | succ current =>
      cases found : hopView hop with
      | none =>
        have no : ¬ passes raw p c ty (current+1) hop := fun h => absentShape found h.2.1
        simp [if_neg no,packedOriginalAdvance,decoded,decodeState,found,
          NumberedWindowPositivePathAlgorithm.advance,encodeState]
      | some payload =>
        obtain ⟨target,q,w,r⟩ := payload
        have eq := passedCalls entries s raw p hr hp c ty current hop target q w r g decoded found
        have out : run hopTarget hop = target := (presentShape found).2.1
        have sourceResult : packedOriginalAdvance entries s c ty (current+1) hop =
            if NumberedWindowConcreteCheckers.step entries s g ty q w r = true ∧
                least s g ty q = some current ∧ least s g ty r = some target
            then some target else none := by
          simp [packedOriginalAdvance,decoded,decodeState,NumberedWindowPositivePathAlgorithm.advance,
            found,Bool.and_eq_true,beq_iff_eq,and_assoc]
        by_cases good : NumberedWindowConcreteCheckers.step entries s g ty q w r = true ∧
            least s g ty q = some current ∧ least s g ty r = some target
        · rw [if_pos (eq.mpr good),out,sourceResult,if_pos good] <;> rfl
        · have bad : ¬ passes raw p c ty (current+1) hop := fun yes => good (eq.mp yes)
          rw [if_neg bad,sourceResult,if_neg good] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceCalibrationProof
