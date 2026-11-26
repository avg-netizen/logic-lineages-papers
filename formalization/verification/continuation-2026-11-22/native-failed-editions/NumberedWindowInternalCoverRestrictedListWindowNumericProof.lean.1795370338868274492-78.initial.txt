module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadGuardNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization List.Vector
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize evalZeroTest actualConjunctionEvaluation)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack unpackNode pack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run applyUnary nodeGood field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue bothAccept)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets (typeOnlyHeadGuard)
open NumberedWindowInternalCoverTypeOnlyHeadGuardNumericProof (exact_CoverTypeOnlyHeadGuardNumeric)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject acceptedHeads)
open NumberedWindowInternalCoverArgumentGuardNumericProof (exact_CoverArgumentGuardNumeric)
open NumberedWindowInternalCoverRestrictedListWindowTargets

private theorem ordinaryField {raw h a : Nat} (read : unpackNode raw = some (4,[h,a])) :
    run (field 1) raw = a := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 4 (pack [h,a]))).2
  have step : run cellTail (pack [h,a]) = pack [a] := (headTailOfCell (cellAt h (pack [a]))).2
  have last : run cellHead (pack [a]) = a := (headTailOfCell (cellAt a (pack []))).1
  change run (field 1) (pair 4 (pack [h,a])+1) = a
  simp only [field,cursor,applyValue,outer,step,last]

private theorem numberedFields {raw h ty k l r : Nat} (read : unpackNode raw = some (5,[h,ty,k,l,r])) :
    run (field 3) raw = l ∧ run (field 4) raw = r := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 5 (pack [h,ty,k,l,r]))).2
  have before : run cellTail (pack [h,ty,k,l,r]) = pack [ty,k,l,r] :=
    (headTailOfCell (cellAt h (pack [ty,k,l,r]))).2
  have second : run cellTail (pack [ty,k,l,r]) = pack [k,l,r] :=
    (headTailOfCell (cellAt ty (pack [k,l,r]))).2
  have third : run cellTail (pack [k,l,r]) = pack [l,r] :=
    (headTailOfCell (cellAt k (pack [l,r]))).2
  have left : run cellHead (pack [l,r]) = l := (headTailOfCell (cellAt l (pack [r]))).1
  have fourth : run cellTail (pack [l,r]) = pack [r] := (headTailOfCell (cellAt l (pack [r]))).2
  have right : run cellHead (pack [r]) = r := (headTailOfCell (cellAt r (pack []))).1
  change run (field 3) (pair 5 (pack [h,ty,k,l,r])+1) = l ∧
    run (field 4) (pair 5 (pack [h,ty,k,l,r])+1) = r
  simp only [field,cursor,applyValue,outer,before,second,third,left,fourth,right] <;> simp

theorem exact_TypeOnlyArgumentDomain (s : Settings) (a : Nat) :
    run (argumentReject (typeOnlyHeadGuard s)) a = 0 ↔ OriginalTypeOnlyArguments s a := by
  unfold run
  rw [exact_CoverArgumentGuardNumeric]
  have gate : acceptedHeads (typeOnlyHeadGuard s) a = true ↔ OriginalTypeOnlyArguments s a := by
    unfold acceptedHeads OriginalTypeOnlyArguments
    cases eq : unpack a with
    | none => simp [eq]
    | some xs =>
      simp only [Option.any_some,List.all_eq_true]
      constructor
      · intro h
        exact ⟨xs,rfl,fun q hq =>
          (exact_CoverTypeOnlyHeadGuardNumeric s q).mp (by simpa using h q hq)⟩
      · rintro ⟨ys,read,h⟩
        have same := Option.some.inj read
        subst ys
        intro q hq
        have yes := (exact_CoverTypeOnlyHeadGuardNumeric s q).mpr (h q hq)
        change (evaluate (typeOnlyHeadGuard s) (q ::ᵥ nil) == 1) = true
        exact beq_iff_eq.mpr yes
  cases test : acceptedHeads (typeOnlyHeadGuard s) a <;> simp_all

private theorem slot (s : Settings) (i raw a : Nat) (picked : run (field i) raw = a) :
    run (listSlotAllowed (typeOnlyHeadGuard s) i) raw = 1 ↔ OriginalTypeOnlyArguments s a := by
  rw [listSlotAllowed,applyValue,applyValue,picked]
  have zero : run GorbowPRInternalControl.zeroTest (run (argumentReject (typeOnlyHeadGuard s)) a) =
      if run (argumentReject (typeOnlyHeadGuard s)) a = 0 then 1 else 0 := evalZeroTest _
  rw [zero,← exact_TypeOnlyArgumentDomain]
  split <;> simp_all

private theorem branchValue (G : Program 1) (B : Program 2) (ctx raw : Nat) :
    evaluate (keepWhenListAllowed G B) (ctx ::ᵥ raw ::ᵥ nil) =
      if run G raw = 1 then evaluate B (ctx ::ᵥ raw ::ᵥ nil) else 0 := by
  rw [keepWhenListAllowed,evalBranch,evalNormalize]
  let xs := ctx ::ᵥ raw ::ᵥ nil
  change (if (if evaluate (onRaw G) xs = 1 then 1 else 0) = 0
    then 0 else evaluate B xs) = (if evaluate (onRaw G) xs = 1 then evaluate B xs else 0)
  by_cases good : evaluate (onRaw G) xs = 1 <;> simp [good]

private theorem headerZero (t k raw : Nat) (miss : run (header t k) raw ≠ 1) :
    run (header t k) raw = 0 := by
  have bit : run (header t k) raw = 0 ∨ run (header t k) raw = 1 := by
    unfold run header nodeGood
    rw [actualConjunctionEvaluation]
    split <;> simp
  exact bit.resolve_right miss

theorem exact_CoverRestrictedListBaseNumeric : ExactCoverRestrictedListBaseNumeric := by
  intro s B calibrated ctx raw
  let G := typeOnlyHeadGuard s
  let xs := ctx ::ᵥ raw ::ᵥ nil
  have rawSelect (P : Program 1) : evaluate (onRaw P) xs = run P raw := rfl
  have reduce (Q : Program 1)
      (same : run Q raw = 1 ↔ OriginalTypeOnlyParentDomain s raw) :
      (OriginalTypeOnlyParentDomain s raw → evaluate (keepWhenListAllowed Q B) xs = intrinsicWindow s ctx raw) ∧
      (¬ OriginalTypeOnlyParentDomain s raw → evaluate (keepWhenListAllowed Q B) xs = 0) := by
    rw [branchValue]
    constructor
    · intro yes
      rw [if_pos (same.mpr yes)]
      exact calibrated ctx raw
    · intro no
      rw [if_neg (fun report => no (same.mp report))]
  change (OriginalTypeOnlyParentDomain s raw → evaluate (restrictedListBase G B) xs = intrinsicWindow s ctx raw) ∧
    (¬OriginalTypeOnlyParentDomain s raw → evaluate (restrictedListBase G B) xs = 0)
  rw [restrictedListBase,evalBranch,rawSelect]
  by_cases ordinary : run (header 4 2) raw = 1
  · rw [ordinary,if_neg (by decide)]
    obtain ⟨fs,read,len⟩ := (exact_CoverHeaderUnpackNode 4 2 raw).mp ordinary
    rcases fs with _ | ⟨h,_ | ⟨a,_ | ⟨_,_⟩⟩⟩ <;> simp at len
    apply reduce
    rw [ordinaryListAllowed,slot s 1 raw a (ordinaryField read)]
    constructor
    · intro allowed
      refine ⟨?_,?_⟩
      · intro hh aa same
        rw [read] at same
        cases same
        exact allowed
      · intro hh tt kk ll rr other
        rw [read] at other
        cases other
    · intro domain
      exact domain.1 h a read
  · rw [headerZero 4 2 raw ordinary,if_pos rfl,evalBranch,rawSelect]
    by_cases numbered : run (header 5 5) raw = 1
    · rw [numbered,if_neg (by decide)]
      obtain ⟨fs,read,len⟩ := (exact_CoverHeaderUnpackNode 5 5 raw).mp numbered
      rcases fs with _ | ⟨h,_ | ⟨ty,_ | ⟨k,_ | ⟨l,_ | ⟨r,_ | ⟨_,_⟩⟩⟩⟩⟩⟩ <;> simp at len
      apply reduce
      have ⟨lv,rv⟩ := numberedFields read
      rw [numberedListAllowed,bothAccept,slot s 3 raw l lv,slot s 4 raw r rv]
      constructor
      · intro allowed
        refine ⟨?_,?_⟩
        · intro hh aa other
          rw [read] at other
          cases other
        · intro hh tt kk ll rr same
          rw [read] at same
          cases same
          exact allowed
      · intro domain
        exact domain.2 h ty k l r read
    · rw [headerZero 5 5 raw numbered,if_pos rfl]
      refine ⟨fun _ => calibrated ctx raw,fun no => False.elim (no ⟨?_,?_⟩)⟩
      · intro h a read
        exact False.elim (ordinary ((exact_CoverHeaderUnpackNode 4 2 raw).mpr ⟨_,read,rfl⟩))
      · intro h ty k l r read
        exact False.elim (numbered ((exact_CoverHeaderUnpackNode 5 5 raw).mpr ⟨_,read,rfl⟩))

#print axioms exact_TypeOnlyArgumentDomain
#print axioms exact_CoverRestrictedListBaseNumeric

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowNumericProof
