import LogicLineages.PersistentMarking.NativeTowerExtractorCodeKernel
import LogicLineages.PersistentMarking.NativeTowerIteratorCodeBridge
import LogicLineages.PersistentMarking.NativeTowerExtractorGeneralProof
import LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof

namespace LogicLineages.PersistentMarking.NativeTowerExtractorCodeBridge
open Spine NativeReduction NativeIteratorTargets NativeIndexedCarrierTargets
open NativeTowerWitnessPrefixTargets NativeTowerExtractorGeneralTargets
open NativeTowerExtractorGeneralProof NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets
open NativeOrdinalExponentialTargets NativeOrdinalExponentialTypingProof
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerTypeCodeBridge (exactNativeTowerTypeCode)
open NativeTowerEraseCodeKernel (boundCode lambdaCode)
open NativeTowerEraseCodeBridge (exactBoundCode exactLambdaCode)
open NativeTowerIteratorCodeKernel (applicationCode iteratorCode)
open NativeTowerIteratorCodeBridge (exactRawApp exactIteratorCode)
open NativeTowerNumericCodeTargets (rawCode)
open NativeTowerExtractorCodeKernel
open NumberedWindowArithmeticTyCode (encodeTy)

private theorem appOrdinary {a b : Ty} {f x : Expr} (hf : Ordinary f) (hx : Ordinary x) :
    Ordinary (app a b f x) := ⟨hf,hx,True.intro⟩

theorem exactOrdinalZeroCode : ordinalZeroCode = rawCode ordinalZero := rfl

theorem lowerOrdinary (j : Nat) : Ordinary (lowerOperand j) := by
  cases j <;> trivial

theorem exactLowerOperandCode (j : Nat) : lowerOperandCode j = rawCode (lowerOperand j) := by
  cases j with
  | zero => exact exactOrdinalZeroCode
  | succ j =>
    simp only [lowerOperandCode,Nat.succ_ne_zero,if_false,lowerOperand]
    rw [exactNativeTowerTypeCode (j+1)]
    exact exactBoundCode _ _

private theorem drainOrdinary (n : Nat) (q : Expr) (hq : Ordinary q) : Ordinary (drain n q) := by
  induction n generalizing q with
  | zero => exact hq
  | succ n ih =>
    exact ih _ (appOrdinary hq (lowerOrdinary n))

theorem exactDrainCode (n : Nat) (q : Expr) (hq : Ordinary q) :
    drainCode n (rawCode q) = rawCode (drain n q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    unfold drainCode
    rw [List.range_succ,List.foldr_append]
    change drainCode n (drainStep n (rawCode q)) = _
    unfold drainStep
    rw [exactNativeTowerTypeCode,exactLowerOperandCode,exactRawApp (ty n) (ty n) hq (lowerOrdinary n)]
    exact ih _ (appOrdinary hq (lowerOrdinary n))

private theorem appliedOrdinary (S : Signature) (n : Nat) {i h x : Expr}
    (hi : Ordinary i) (hh : Ordinary h) (hx : Ordinary x) :
    Ordinary (applied (level n) i h x) :=
  appOrdinary (appOrdinary (appOrdinary
    (NativeIteratorChecks.exact_ClosedNativeIterator S (level n)).1.2.1 hi) hh) hx

theorem exactAppliedCode (S : Signature) (n : Nat) {i h x : Expr}
    (hi : Ordinary i) (hh : Ordinary h) (hx : Ordinary x) :
    appliedCode n (rawCode i) (rawCode h) (rawCode x) = rawCode (applied (level n) i h x) := by
  have it : Ordinary (iterator (level n)) :=
    (NativeIteratorChecks.exact_ClosedNativeIterator S (level n)).1.2.1
  let f := app indexType (ty (n+2)) (iterator (level n)) i
  let g := app (ty (n+1)) (ty (n+1)) f h
  have hf : Ordinary f := appOrdinary it hi
  have hg : Ordinary g := appOrdinary hf hh
  unfold appliedCode
  rw [exactNativeTowerTypeCode n,exactNativeTowerTypeCode (n+1),exactNativeTowerTypeCode 0,
    exactNativeTowerTypeCode (n+2),exactIteratorCode S,
    exactRawApp (ty 0) (ty (n+2)) it hi]
  change applicationCode (encodeTy (ty n)) (encodeTy (ty n))
    (applicationCode (encodeTy (ty (n+1))) (encodeTy (ty (n+1))) (rawCode f) (rawCode h))
      (rawCode x) = _
  rw [exactRawApp (ty (n+1)) (ty (n+1)) hf hh]
  exact exactRawApp (ty n) (ty n) hg hx

theorem exactInnerCode (S : Signature) (n : Nat) :
    innerCode n = rawCode (inner n) := by
  unfold innerCode
  rw [show typeCode 0 = encodeTy indexType from exactNativeTowerTypeCode 0,
    exactNativeTowerTypeCode (n+1),exactBoundCode indexType 0,exactBoundCode (ty (n+1)) (n+1),
    exactLowerOperandCode]
  rw [exactAppliedCode S n (i := .bound indexType 0) (h := .bound (ty (n+1)) (n+1))
    (x := lowerOperand n) True.intro True.intro (lowerOrdinary n)]
  exact exactDrainCode n _ (appliedOrdinary S n True.intro True.intro (lowerOrdinary n))

theorem exactBindAscendingCode (count first : Nat) (q : Expr) (hq : Ordinary q) :
    bindAscendingCode count first (rawCode q) = rawCode (bindAscending count first q) := by
  induction count generalizing first q with
  | zero => rfl
  | succ count ih =>
    unfold bindAscendingCode
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,List.foldl_cons,Nat.add_zero]
    rw [show ((first + ·) ∘ Nat.succ) = ((first+1)+·) by
      funext j
      simp only [Function.comp_apply,Nat.succ_eq_add_one]
      omega]
    change bindAscendingCode count (first+1) (binderStep (rawCode q) first) = _
    unfold binderStep
    rw [exactNativeTowerTypeCode,exactLambdaCode _ hq]
    exact ih (first+1) (.lam (ty first) q) hq

theorem exactExtractorCode (S : Signature) (n : Nat) :
    extractorCode (rawCode ordinalFix) n = rawCode (extractor n) := by
  have hi : Ordinary (inner n) :=
    drainOrdinary n _ (appliedOrdinary S n True.intro True.intro (lowerOrdinary n))
  have hFix : Ordinary ordinalFix := (fixClosed S).1.2.1
  have hb : Ordinary (app endo endo ordinalFix (.lam indexType (inner n))) :=
    appOrdinary hFix hi
  unfold extractorCode
  rw [show typeCode 1 = encodeTy endo from exactNativeTowerTypeCode 1,
    show typeCode 0 = encodeTy indexType from exactNativeTowerTypeCode 0,
    exactInnerCode S,exactLambdaCode _ hi,
    exactRawApp endo endo (f := ordinalFix) (x := .lam indexType (inner n)) hFix hi]
  exact exactBindAscendingCode (n+1) 1 _ hb

#print axioms exactDrainCode
#print axioms exactAppliedCode
#print axioms exactInnerCode
#print axioms exactBindAscendingCode
#print axioms exactExtractorCode
end LogicLineages.PersistentMarking.NativeTowerExtractorCodeBridge
