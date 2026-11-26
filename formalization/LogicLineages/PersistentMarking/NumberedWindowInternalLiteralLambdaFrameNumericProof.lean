module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)
open NumberedWindowFieldAlgorithm (unpackNode pack packNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation compositeTwo)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot sameSlot encodeFrame)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot sameSlotOne)
open NumberedWindowInternalSparseRawTickTargets (ActualFallback)
open NumberedWindowInternalSparseRawTick (fallbackValue)
open NumberedWindowRawContextAlgorithm (next context Frame)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralLambdaFrameProof

private theorem lambdaOne (f : Nat) :
    run rawLambdaShape f = 1 ↔ ∃ t b, unpackNode f = some (2,[t,b]) := by
  rw [rawLambdaShape,nodeArity _ 2 f 2 (literalEvaluation 1 2 (f ::ᵥ nil))]
  constructor
  · rintro ⟨fs,h,len⟩
    rcases fs with _ | ⟨a,_ | ⟨b,_ | ⟨z,more⟩⟩⟩ <;> simp at len
    exact ⟨a,b,h⟩
  · rintro ⟨t,b,h⟩
    exact ⟨[t,b],h,rfl⟩

private theorem lambdaFields {f t b : Nat} (h : unpackNode f = some (2,[t,b])) :
    run (field 0) f = t ∧ run (field 1) f = b := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 2 (pack [t,b]))).2
  have first : run cellHead (pack [t,b]) = t ∧ run cellTail (pack [t,b]) = pack [b] :=
    headTailOfCell (cellAt t (pack [b]))
  have last : run cellHead (pack [b]) = b := (headTailOfCell (cellAt b (pack []))).1
  change run (field 0) (pair 2 (pack [t,b]) + 1) = t ∧ _
  simp only [field,cursor,applyValue,packNode,outer,first.1,first.2,last,and_self]

private theorem witnessOne (w : Nat) :
    run lambdaWitnessShape w = 1 ↔ ∃ c, unpackNode w = some (1,[c]) := by
  rw [lambdaWitnessShape,nodeArity _ 1 w 1 (literalEvaluation 1 1 (w ::ᵥ nil))]
  constructor
  · rintro ⟨fs,h,len⟩
    rcases fs with _ | ⟨a,_ | ⟨b,rest⟩⟩ <;> simp at len
    exact ⟨a,h⟩
  · rintro ⟨c,h⟩
    exact ⟨[c],h,rfl⟩

private theorem witnessChild {w k : Nat} (h : unpackNode w = some (1,[k])) :
    run (field 0) w = k := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 1 (pack [k]))).2
  have inner : run cellHead (pack [k]) = k := (headTailOfCell (cellAt k (pack []))).1
  change run (field 0) (pair 1 (pack [k]) + 1) = k
  simp only [field,cursor,applyValue,outer,inner]

private theorem frameAccepted (q w r : Nat) :
    evaluate lambdaFrameGuard (tape q w r) = 1 ↔
      ∃ d a b, unpackNode q = some (2,[d,a]) ∧ unpackNode r = some (2,[d,b]) := by
  simp only [lambdaFrameGuard,conjunctionOne,atSlot,sameSlotOne]
  change (run rawLambdaShape q = 1 ∧ run rawLambdaShape r = 1 ∧ run (field 0) q = run (field 0) r) ↔ _
  rw [lambdaOne,lambdaOne]
  constructor
  · rintro ⟨⟨d,a,p⟩,⟨e,b,h⟩,eq⟩
    rw [(lambdaFields p).1,(lambdaFields h).1] at eq
    exact ⟨d,a,b,p,eq.symm ▸ h⟩
  · rintro ⟨d,a,b,p,h⟩
    exact ⟨⟨d,a,p⟩,⟨d,b,h⟩,(lambdaFields p).1.trans (lambdaFields h).1.symm⟩

private theorem frameBit (q w r : Nat) :
    evaluate lambdaFrameGuard (tape q w r) = 0 ∨ evaluate lambdaFrameGuard (tape q w r) = 1 := by
  unfold lambdaFrameGuard
  rw [conjunctionEvaluation]
  split <;> simp

private theorem witnessBit (q w r : Nat) :
    evaluate lambdaWitnessTest (tape q w r) = 0 ∨ evaluate lambdaWitnessTest (tape q w r) = 1 := by
  rw [lambdaWitnessTest,atSlot]
  change run lambdaWitnessShape w = 0 ∨ run lambdaWitnessShape w = 1
  unfold lambdaWitnessShape run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

private theorem consValue (p q : Program 3) (v : List.Vector Nat 3) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

private theorem emitValue (q w r a c b : Nat)
    (src : run (field 1) q = a) (witness : run (field 0) w = c) (dst : run (field 1) r = b) :
    evaluate emitLambdaFrame (tape q w r) = encodeFrame (some (a,c,b)) := by
  let p := consOf (frameSlot 1 0) (consOf (frameSlot 0 1) (consOf (frameSlot 1 2) (constantZero 3)))
  change Nat.succ (List.Vector.ofFn (fun _ : Fin 1 => evaluate p (tape q w r))).head = _
  rw [vectorOne]
  change Nat.succ (evaluate p (tape q w r)) = _
  simp only [p,consValue,frameSlot,atSlot]
  change Nat.succ (pair (run (field 1) q)
    (pair (run (field 0) w) (pair (run (field 1) r) 0 + 1) + 1) + 1) = _
  rw [src,witness,dst]
  rfl

private theorem detectContext (q r c a w b : Nat)
    (hit : next 1 [c] q r = some (a,w,b)) :
    w = c ∧ ∃ d, unpackNode q = some (2,[d,a]) ∧ unpackNode r = some (2,[d,b]) := by
  unfold next at hit
  cases qx : unpackNode q with
  | none => simp [qx] at hit
  | some src =>
    cases rx : unpackNode r with
    | none => simp [qx,rx] at hit
    | some dst =>
      simp only [qx,rx,Option.bind_eq_bind,Option.bind_some] at hit
      rcases src with ⟨t,x⟩
      rcases dst with ⟨k,y⟩
      rcases t with _ | _ | _ | t <;> rcases k with _ | _ | _ | k <;> try simp [context] at hit
      rcases x with _ | ⟨d,_ | ⟨a',_ | ⟨p,z⟩⟩⟩ <;>
        rcases y with _ | ⟨e,_ | ⟨b',_ | ⟨l,m⟩⟩⟩ <;> simp [context] at hit
      rcases hit with ⟨rfl,rfl,rfl,rfl⟩
      exact ⟨rfl,_,rfl,rfl⟩

/-- The actual selected open lambda frame agrees with the original
tag-one context row on every raw q/r and exact original witness. -/
theorem exact_LiteralLambdaFrameValue (q w r child : Nat)
    (witness : unpackNode w = some (1,[child])) :
    evaluate chosenLambdaFrame (tape q w r) = encodeFrame (next 1 [child] q r) := by
  rcases frameBit q w r with no | yes
  · rw [chosenLambdaFrame,evalBranch,no,if_pos rfl]
    cases h : next 1 [child] q r with
    | none => rfl
    | some p =>
      obtain ⟨a,c,b⟩ := p
      obtain ⟨_,d,p,h⟩ := detectContext q r child a c b h
      have bad := (frameAccepted q w r).mpr ⟨d,a,b,p,h⟩
      exact Nat.noConfusion (no.symm.trans bad)
  · obtain ⟨d,a,b,p,h⟩ := (frameAccepted q w r).mp yes
    have value : next 1 [child] q r = some (a,child,b) := by simp [next,context,p,h]
    rw [chosenLambdaFrame,evalBranch,yes,if_neg (by decide : (1 : Nat) ≠ 0),value]
    exact emitValue q w r a child b (lambdaFields p).2 (witnessChild witness) (lambdaFields h).2

private theorem headerFromView {q tag : Nat} {fs : List Nat} (view : unpackNode q = some (tag,fs)) :
    run cellHead q = tag := by
  rw [codeOfNode view]
  exact (headTailOfCell (cellAt tag (pack fs))).1

private theorem lambdaHeadValue (q w r : Nat) :
    evaluate lambdaHeadTest (tape q w r) = (if run cellHead q = 2 then 1 else 0) := by
  rw [lambdaHeadTest,atSlot]
  unfold run
  change evaluate equalityTest (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((![cellHead,literal 1 2] : Fin 2 → Program 1) i) (q ::ᵥ nil)) = _
  rw [vectorTwo]
  change evaluate equalityTest (evaluate cellHead (q ::ᵥ nil) ::ᵥ evaluate (literal 1 2) (q ::ᵥ nil) ::ᵥ nil) = _
  rw [literalEvaluation,exactEqualityEvaluation]

private theorem lambdaOtherRejected (q w r : Nat) (head : run cellHead q = 2)
    (miss : ¬ ∃ c, unpackNode w = some (1,[c])) : fallbackValue q w r = none := by
  cases wr : unpackNode w with
  | none => simp [fallbackValue,wr]
  | some p =>
    rcases p with ⟨tag,fs⟩
    cases qr : unpackNode q with
    | none => simp [fallbackValue,next,wr,qr]
    | some p =>
      rcases p with ⟨t,args⟩
      have e := (headerFromView qr).symm.trans head
      subst t
      have miss' : ¬ ∃ c, (tag,fs) = (1,[c]) := by simpa [wr] using miss
      simp only [fallbackValue,next,wr,qr,Option.bind_eq_bind,Option.bind_some]
      cases rr : unpackNode r with
      | none => rfl
      | some dst =>
        simp only [Option.bind_eq_bind,Option.bind_some]
        rcases dst with ⟨dt,ds⟩
        unfold context
        split <;> try rfl
        case h_1 => exact False.elim (miss' ⟨_,rfl⟩)
        all_goals simp_all

theorem exact_LiteralLambdaFallback (other : Program 3) (old : ActualFallback other) :
    ActualFallback (lambdaFallback other) := by
  intro q w r
  rcases witnessBit q w r with no | yes
  · rw [lambdaFallback,evalBranch,no,if_pos rfl,otherLambdaCases,evalBranch,lambdaHeadValue]
    by_cases h : run cellHead q = 2
    · have miss : ¬ ∃ c, unpackNode w = some (1,[c]) := by
        intro proof
        have yes := (witnessOne w).mpr proof
        rw [lambdaWitnessTest,atSlot] at no
        change run lambdaWitnessShape w = 0 at no
        rw [yes] at no
        cases no
      rw [if_pos h,if_neg (by decide : (1 : Nat) ≠ 0),lambdaOtherRejected q w r h miss]
      rfl
    · rw [if_neg h,if_pos rfl]
      exact old q w r
  · have pick := yes
    rw [lambdaWitnessTest,atSlot] at pick
    obtain ⟨c,witness⟩ := (witnessOne w).mp pick
    rw [lambdaFallback,evalBranch,yes,if_neg (by decide : (1 : Nat) ≠ 0)]
    rw [exact_LiteralLambdaFrameValue q w r c witness]
    simp only [fallbackValue,witness,Option.bind_eq_bind,Option.bind_some]

#print axioms exact_LiteralLambdaFrameValue
#print axioms exact_LiteralLambdaFallback
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameNumericProof
