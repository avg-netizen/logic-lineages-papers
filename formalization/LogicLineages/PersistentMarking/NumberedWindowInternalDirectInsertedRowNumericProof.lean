module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRow
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (branch constantZero conjunction)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalDirectInsertedRowTargets
open NumberedWindowInternalDirectWitnessEnvelopeTargets (rawTriple guardAt)
open NumberedWindowInternalDirectWitnessEnvelope (exactRawTriple)
open NumberedWindowInternalSparsePathEnvelope (field run)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne chooseBranch literal predOne zeroAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (bothEvaluation branchEvaluation literalEvaluation predEvaluation zeroEvaluation
    compositeOne compositeTwo compositeThree)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowDirectAlgorithm (readEntry)
open NumberedMultisetNumeric (numbersNumber decodeNumbers)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)

private theorem readExact (n : Nat) : rawTriple 4 n = readEntry n := by
  rw [exactRawTriple]
  unfold readEntry
  cases h : unpackNode n with
  | none => rfl
  | some p =>
    obtain ⟨tag,xs⟩ := p
    rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      rcases tag with _ | _ | _ | _ | _ | tag <;> rfl

private theorem conValue {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs =
      (if evaluate p xs = 1 ∧ evaluate q xs = 1 then 1 else 0) :=
  bothEvaluation p q xs

private theorem parseValue (removed row : Nat) :
    evaluate parseRemoved (removed ::ᵥ row ::ᵥ nil) = encodeResult (unpack removed) := by
  change evaluate (.composition parser (Fin.cons (.projection 0) Fin.elim0))
    (removed ::ᵥ row ::ᵥ nil) = _
  rw [compositeOne parser (.projection 0)]
  exact exact_ActualEncodedOutput removed

private theorem readyValue (removed row : Nat) :
    evaluate poolReady (removed ::ᵥ row ::ᵥ nil) = if (unpack removed).isSome then 1 else 0 := by
  change evaluate (chooseBranch parseRemoved (zeroAt 2) (literal 2 1)) _ = _
  rw [branchEvaluation,parseValue,zeroEvaluation,literalEvaluation]
  cases unpack removed <;> rfl

private theorem poolValue (removed row : Nat) (xs : List Nat) (h : unpack removed = some xs) :
    evaluate poolCode (removed ::ᵥ row ::ᵥ nil) = numbersNumber xs := by
  change evaluate (.composition predOne (Fin.cons parseRemoved Fin.elim0))
    (removed ::ᵥ row ::ᵥ nil) = _
  rw [compositeOne predOne parseRemoved,parseValue,h]
  exact predEvaluation (numbersNumber xs + 1)

private theorem rightValue (p : Program 1) (removed row : Nat) :
    evaluate (liftRight p) (removed ::ᵥ row ::ᵥ nil) = run p row := by
  change evaluate (.composition p (Fin.cons (.projection 1) Fin.elim0))
    (removed ::ᵥ row ::ᵥ nil) = _
  rw [compositeOne p (.projection 1)] <;> rfl

private theorem memberValue (removed row : Nat) (xs : List Nat) (dom : Nat)
    (hu : unpack removed = some xs) (hd : run (field 1) row = dom) :
    evaluate memberAt (removed ::ᵥ row ::ᵥ nil) = (xs.any (fun a => a == dom)).toNat := by
  change evaluate (.composition scratchMember
    (Fin.cons poolCode (Fin.cons (liftRight (field 1)) Fin.elim0)))
      (removed ::ᵥ row ::ᵥ nil) = _
  rw [compositeTwo scratchMember poolCode (liftRight (field 1)),
    poolValue removed row xs hu,rightValue,hd]
  have hm := exact_AllInputScratchMembership (numbersNumber xs) dom
  rw [numbersRoundTrip] at hm
  exact hm

private theorem posValue (r : Program 3) (removed row t dom w : Nat)
    (ht : run (field 0) row = t) (hd : run (field 1) row = dom) (hw : run (field 2) row = w) :
    evaluate (positiveAt r) (removed ::ᵥ row ::ᵥ nil) = evaluate r (dom ::ᵥ w ::ᵥ t ::ᵥ nil) := by
  change evaluate (.composition r
    (Fin.cons (liftRight (field 1))
      (Fin.cons (liftRight (field 2)) (Fin.cons (liftRight (field 0)) Fin.elim0))))
        (removed ::ᵥ row ::ᵥ nil) = _
  rw [compositeThree r (liftRight (field 1)) (liftRight (field 2)) (liftRight (field 0)),
    rightValue (field 1),rightValue (field 2),rightValue (field 0),ht,hd,hw]

theorem exactNumericInsertedRow : ExactNumericInsertedRow := by
  intro r removed row
  let args := removed ::ᵥ row ::ᵥ nil
  have hrow : evaluate rowGuard args = run (guardAt 4) row := rightValue _ _ _
  change evaluate (insertedRow r) args = _
  simp only [insertedRow,conValue,hrow]
  have decoded := readExact row
  unfold expected
  rw [← decoded]
  by_cases htag : run (guardAt 4) row = 1
  · simp only [rawTriple,htag,if_true]
    cases hpool : unpack removed with
    | none =>
      have ready := readyValue removed row
      rw [hpool] at ready
      change evaluate poolReady args = 0 at ready
      simp [hpool,htag,ready]
    | some pool =>
      have ready := readyValue removed row
      rw [hpool] at ready
      change evaluate poolReady args = 1 at ready
      have mp := memberValue removed row pool (run (field 1) row) hpool rfl
      have pp := posValue r removed row (run (field 0) row) (run (field 1) row)
        (run (field 2) row) rfl rfl rfl
      change evaluate memberAt args = _ at mp
      change evaluate (positiveAt r) args = _ at pp
      simp only [hpool,htag,ready,mp,pp]
      cases flag : pool.any (fun a => a == run (field 1) row) <;>
        by_cases hp : evaluate r
          (run (field 1) row ::ᵥ run (field 2) row ::ᵥ run (field 0) row ::ᵥ nil) = 1 <;>
        simp [flag,hp]
  · simp only [rawTriple,htag,if_false]
    cases unpack removed <;> simp

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRow
