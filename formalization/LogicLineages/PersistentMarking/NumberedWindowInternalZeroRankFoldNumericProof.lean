module

public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldIterationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFoldNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalListCodec (consCode headCode tailCode)
open InternalListCodecEvaluationProof (consEvaluation)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePositiveFold (initial scratchCursor scratchCurrent onCursor dead)
open NumberedWindowInternalSparsePositiveFoldTargets (encodeScratch)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
open NumberedWindowInternalSparsePositiveFoldIterationProof (repeatStates)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankAdvance (zeroOutput)

private def advanceValue (A : Program 4) (c ty current hop : Nat) : Nat :=
  evaluate A (c ::ᵥ ty ::ᵥ current ::ᵥ hop ::ᵥ nil)

private def nextA (A : Program 4) (c ty : Nat) (p : Nat × Nat) : Nat × Nat :=
  if p.1 = 0 then p
  else if run cellGood p.1 = 0 then (0,0)
  else (run cellTail p.1,advanceValue A c ty p.2 (run cellHead p.1))

private theorem advanced (A : Program 4) (k cursor current c ty start orig : Nat) :
    eval6 (advanceAt A) k (encodeScratch cursor current) c ty start orig =
      advanceValue A c ty current (run cellHead cursor) := by
  unfold eval6 advanceAt
  rw [evaluate,vectorFour]
  change advanceValue A c ty
    (eval6 scratchCurrent k (encodeScratch cursor current) c ty start orig)
    (eval6 (onCursor cellHead) k (encodeScratch cursor current) c ty start orig) = _
  rw [currentValue,onCursorValue]

private theorem updated (A : Program 4) (k cursor current c ty start orig : Nat) :
    eval6 (updateAt A) k (encodeScratch cursor current) c ty start orig =
      encodeScratch (run cellTail cursor) (advanceValue A c ty current (run cellHead cursor)) := by
  unfold updateAt eval6
  rw [evaluate,vectorTwo]
  change evaluate consCode (eval6 (onCursor cellTail) k (encodeScratch cursor current) c ty start orig ::ᵥ
    eval6 (advanceAt A) k (encodeScratch cursor current) c ty start orig ::ᵥ nil) = _
  rw [onCursorValue,advanced,consEvaluation] <;> rfl

private theorem stepValue (A : Program 4) (k cursor current c ty start orig : Nat) :
    eval6 (stepAt A) k (encodeScratch cursor current) c ty start orig =
      let next := nextA A c ty (cursor,current)
      encodeScratch next.1 next.2 := by
  unfold stepAt eval6
  rw [evalBranch]
  change (if eval6 scratchCursor k (encodeScratch cursor current) c ty start orig = 0 then
    encodeScratch cursor current else
    eval6 (branch (onCursor cellGood) dead (updateAt A)) k
      (encodeScratch cursor current) c ty start orig) = _
  rw [cursorValue]
  by_cases nilCursor : cursor = 0
  · simp [nextA,nilCursor]
  rw [if_neg nilCursor]
  unfold eval6
  rw [evalBranch]
  change (if eval6 (onCursor cellGood) k (encodeScratch cursor current) c ty start orig = 0 then
    eval6 dead k (encodeScratch cursor current) c ty start orig else
    eval6 (updateAt A) k (encodeScratch cursor current) c ty start orig) = _
  rw [onCursorValue,deadValue,updated]
  by_cases good : run cellGood cursor = 0 <;> simp [nextA,nilCursor,good]

private theorem iterateValue (A : Program 4) (fuel c ty start orig : Nat) :
    evaluate (iterateAt A) (fuel ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil) =
      let final := repeatStates (nextA A c ty) fuel (orig,start)
      encodeScratch final.1 final.2 := by
  induction fuel with
  | zero => exact initialValue c ty start orig
  | succ n ih =>
    change eval6 (stepAt A) n
      (evaluate (iterateAt A) (n ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil))
      c ty start orig = _
    rw [ih]
    exact stepValue A n _ _ c ty start orig

private theorem chosenValue (A : Program 4) (c ty start cert : Nat) :
    evaluate (stateAt A) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      let final := repeatStates (nextA A c ty) cert (cert,start)
      encodeScratch final.1 final.2 := by
  unfold stateAt
  rw [evaluate,vectorFive]
  exact iterateValue A cert c ty start cert

private theorem chosenCoordinate (A : Program 4) (p : Program 1) (c ty start cert : Nat) :
    evaluate (.composition p (fun _ : Fin 1 => stateAt A)) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      run p (evaluate (stateAt A) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil)) := by
  rw [evaluate,vectorOne] <;> rfl

private def finishPair (p : Nat × Nat) : Nat := if p.1 = 0 then p.2 else 0

private theorem finishValue (A : Program 4) (c ty start cert : Nat) :
    evaluate (finishAt A) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      finishPair (repeatStates (nextA A c ty) cert (cert,start)) := by
  unfold finishAt
  rw [evalBranch,chosenCoordinate,chosenCoordinate,chosenValue,scratchHead,scratchTail]
  rfl

private theorem walkValue (A : Program 4) (c ty source cert target : Nat) :
    evaluate (walkAt A) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      finishPair (repeatStates (nextA A c ty) cert (cert,source+1)) := by
  unfold walkAt
  rw [evaluate,vectorFour]
  exact finishValue A c ty (source+1) cert

private theorem positiveValue (A : Program 4) (c ty source cert target : Nat) :
    evaluate (positiveAt A) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      if cert ≠ 0 ∧ finishPair (repeatStates (nextA A c ty) cert (cert,source+1)) = target+1
      then 1 else 0 := by
  unfold positiveAt
  rw [conjunctionEvaluation,evalBranch]
  have compared :
      evaluate (.composition InternalEqualityTest.equalityTest
        ![walkAt A,.composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))])
        (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      if finishPair (repeatStates (nextA A c ty) cert (cert,source+1)) = target+1 then 1 else 0 := by
    rw [evaluate,vectorTwo]
    change evaluate InternalEqualityTest.equalityTest
      (evaluate (walkAt A) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) ::ᵥ
        (target+1) ::ᵥ nil) = _
    rw [walkValue,exactEqualityEvaluation]
  change (if (if cert = 0 then 0 else 1) = (1 : Nat) ∧
    evaluate (.composition InternalEqualityTest.equalityTest
        ![walkAt A,.composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))])
        (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) = 1 then 1 else 0) = _
  rw [compared]
  by_cases nz : cert = 0 <;> by_cases eq :
    finishPair (repeatStates (nextA A c ty) cert (cert,source+1)) = target+1 <;> simp [nz,eq]

private theorem filtered (g : Program 1) (A : Program 4) (c ty cur hop : Nat) :
    advanceValue (zeroOutput g A) c ty cur hop = advanceValue A c ty cur hop ∨
      advanceValue (zeroOutput g A) c ty cur hop = 0 := by
  unfold advanceValue zeroOutput
  rw [evalBranch]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem ordinaryDead (raw : Program 5) (least : Program 3) (c ty hop : Nat) :
    advanceValue (advance raw least) c ty 0 hop = 0 := by
  classical
  unfold advanceValue
  change NumberedWindowInternalSparsePathAdvanceEvaluationProof.eval4 (advance raw least) c ty 0 hop = 0
  rw [NumberedWindowInternalSparsePathAdvanceEvaluationProof.resultValue]
  simp [NumberedWindowInternalSparsePathAdvanceEvaluationProof.passes]

private theorem stepRelated (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty : Nat) (x y : Nat × Nat) (h : x = y ∨ x.2 = 0) :
    nextA (zeroOutput g (advance raw least)) c ty x = nextA (advance raw least) c ty y ∨
      (nextA (zeroOutput g (advance raw least)) c ty x).2 = 0 := by
  rcases x with ⟨cursor,current⟩
  rcases h with e | deadCurrent
  · subst y
    unfold nextA
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    rcases filtered g (advance raw least) c ty current (run cellHead cursor) with same | zero
    · exact Or.inl (congrArg (Prod.mk (run cellTail cursor)) same)
    · exact Or.inr zero
  · right
    change current = 0 at deadCurrent
    unfold nextA
    split
    · exact deadCurrent
    split
    · rfl
    · rcases filtered g (advance raw least) c ty current (run cellHead cursor) with same | zero
      · rw [deadCurrent,ordinaryDead] at same
        change advanceValue (zeroOutput g (advance raw least)) c ty current (run cellHead cursor) = 0
        rw [deadCurrent]
        exact same
      · exact zero

private theorem iterationsRelated (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty start cert fuel : Nat) :
    let x := repeatStates (nextA (zeroOutput g (advance raw least)) c ty) fuel (cert,start)
    let y := repeatStates (nextA (advance raw least) c ty) fuel (cert,start)
    x = y ∨ x.2 = 0 := by
  induction fuel with
  | zero => exact Or.inl rfl
  | succ n ih => exact stepRelated g raw least c ty _ _ ih

/-- The original fuel/certificate and actual code of the successful
destination are unchanged. Numerical result only; this is not an object
arithmetic derivation for an open address. -/
theorem exact_ZeroRankPositiveImpliesOrdinaryNumeric (g : Program 1) (raw : Program 5)
    (least : Program 3) (c ty source cert target : Nat)
    (held : evaluate (zeroPositive g raw least) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) = 1) :
    evaluate (NumberedWindowInternalSparsePositiveFold.positive raw least)
      (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) = 1 := by
  rw [zeroPositive,positiveValue] at held
  rw [← exact_OriginalParameterizedPositive,positiveValue]
  split at held
  · rename_i accepted
    obtain ⟨nz,live⟩ := accepted
    rcases iterationsRelated g raw least c ty (source+1) cert cert with eq | dz
    · rw [eq] at live
      simp [nz,live]
    · have impossible : finishPair
          (repeatStates (nextA (zeroOutput g (advance raw least)) c ty) cert (cert,source+1)) = 0 := by
        unfold finishPair
        split
        · exact dz
        · rfl
      rw [impossible] at live
      cases live
  · contradiction

#print axioms exact_ZeroRankPositiveImpliesOrdinaryNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFoldNumericProof
