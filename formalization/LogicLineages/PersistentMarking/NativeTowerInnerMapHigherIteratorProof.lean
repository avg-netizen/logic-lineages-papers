import LogicLineages.PersistentMarking.NativeTowerInnerMapSubstitutionProof
import LogicLineages.PersistentMarking.NativeTowerIndexedEntryProof
import LogicLineages.PersistentMarking.NativeIteratorStrictChecks
import LogicLineages.PersistentMarking.NativeClosedApplicationChecks
import LogicLineages.PersistentMarking.NativeIndexedCarrierSubtype

namespace LogicLineages.PersistentMarking.NativeTowerInnerMapHigherIteratorProof
open Spine NativeReduction StructuralContext NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeClosedApplication NativeIndexedCarrierSubtype
open NativeTowerWitnessPrefixTargets NativeOrdinalArithmeticTargets NativeTowerBetaPathTargets NativeTowerBetaPathProof
open NativeTowerIndexedEntryTargets NativeTowerIndexedEntryProof NativeTowerInnerMapSubstitutionProof

/-- Reinstall all actual lower arguments with their original types and
positions, from the highest remaining argument to the literal terminal Z. -/
def applyPaidDrain (S : Signature) : (k : Nat) → ClosedNativeTerm S (ty k) →
    ClosedNativeTerm S indexType
  | 0, q => q
  | k+1, q => applyPaidDrain S k (applyClosed q (paidOperand S k))

theorem exact_OriginalPaidDrainLiteral (S : Signature) (k : Nat) :
    ∀ q : ClosedNativeTerm S (ty k), (applyPaidDrain S k q).val = filledDrain k q.val := by
  induction k with
  | zero => intro q; rfl
  | succ k ih =>
    intro q
    rw [applyPaidDrain,ih]
    change filledDrain k (app (ty k) (ty k) q.val (paidOperand S k).val) =
      filledDrain k (app (ty k) (ty k) q.val (operandValue k))
    rw [paidOperandLiteral]

private theorem liftOne {S : Signature} {σ τ : Ty}
    (before after : ClosedNativeTerm S (.arrow σ τ)) (arg : ClosedNativeTerm S σ)
    (raw : Reduction S before.val after.val) (strict : NativeBelow after before) :
    Reduction S (applyClosed before arg).val (applyClosed after arg).val ∧
      NativeBelow (applyClosed after arg) (applyClosed before arg) := by
  let C : Context := .head (.app σ τ) .nil .hole (.cons arg.val .nil)
  have typed : ContextTyped S C (.arrow σ τ) τ :=
    .head .hole ⟨0,rfl⟩ .nil True.intro True.intro (.cons arg.property.1.1.1 .nil)
      ⟨arg.property.1.1.2,True.intro⟩ ⟨arg.property.1.2.1,True.intro⟩ rfl
  have lifted : Reduction S (applyClosed before arg).val (applyClosed after arg).val := by
    change Reduction S (fill C before.val) (fill C after.val)
    exact .context typed before.property.1.1 after.property.1.1 raw
  exact ⟨lifted,
    NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S σ τ before after arg strict⟩

private theorem liftDrain (S : Signature) (k : Nat) :
    ∀ (before after : ClosedNativeTerm S (ty k)),
      Reduction S before.val after.val → NativeBelow after before →
      Reduction S (applyPaidDrain S k before).val (applyPaidDrain S k after).val ∧
        NativeBelow (applyPaidDrain S k after) (applyPaidDrain S k before) := by
  induction k with
  | zero => intro before after raw strict; exact ⟨raw,strict⟩
  | succ k ih =>
    intro before after raw strict
    have step := liftOne before after (paidOperand S k) raw strict
    exact ih _ _ step.1 step.2

/-- Exact higher-level carrier in the original inner body, with real supplied
index j, original actual h at the head and actual h_l (or Z) as its seed. -/
def printedIndexedHead (S : Signature) (l : Nat) (j : ClosedNativeTerm S indexType) :
    ClosedNativeTerm S (ty l) :=
  indexedTerm (level l) (actualArg S l) (paidOperand S l) j

theorem exact_OriginalHigherIteratorEndpoint (S : Signature) (l : Nat)
    (j : ClosedNativeTerm S indexType) :
    (applyPaidDrain S l (printedIndexedHead S l j)).val =
      filledDrain l (indexedW (level l) (binderArg l) (operandValue l) j.val) := by
  rw [exact_OriginalPaidDrainLiteral]
  change filledDrain l (indexedW (level l) (actualArg S l).val (paidOperand S l).val j.val) = _
  rw [actualArgLiteral,paidOperandLiteral]

/-- The actual first index beta and the exact three higher-type iterator
steps, lifted through each unchanged original function slot. -/
theorem exact_OriginalInnerMapHigherIteratorRun (S : Signature) (l : Nat)
    (mapping : ClosedNativeTerm S endo) (j : ClosedNativeTerm S indexType)
    (mapValue : mapping.val = innerMap l) :
    StrictRun S 4 (applyClosed mapping j) (applyPaidDrain S l (printedIndexedHead S l j)) := by
  obtain ⟨first,firstValue,firstRaw,firstStrict⟩ := exact_OriginalInnerMapApplicationBeta S l mapping j mapValue
  let P := actualArg S l
  let U := paidOperand S l
  obtain ⟨start,atIndex,atFunction,finish,startValue,indexValue,functionValue,finishValue,
    firstIteratorStrict,secondIteratorStrict,thirdIteratorStrict⟩ :=
    NativeIteratorStrictChecks.exact_IteratorNativeStrictChain S (level l)
      j.val P.val U.val j.property P.property U.property
  obtain ⟨firstIteratorRaw,secondIteratorRaw,thirdIteratorRaw⟩ :=
    NativeIteratorChecks.exact_IteratorNativeBetaTransport S (level l)
      j.val P.val U.val j.property P.property U.property
  have e₁ : Reduction S start.val atIndex.val := by
    rw [startValue,indexValue]; exact firstIteratorRaw
  have e₂ : Reduction S atIndex.val atFunction.val := by
    rw [indexValue,functionValue]; exact secondIteratorRaw
  have e₃ : Reduction S atFunction.val finish.val := by
    rw [functionValue,finishValue]; exact thirdIteratorRaw
  have inside₁ := liftDrain S l start atIndex e₁ firstIteratorStrict
  have inside₂ := liftDrain S l atIndex atFunction e₂ secondIteratorStrict
  have inside₃ := liftDrain S l atFunction finish e₃ thirdIteratorStrict
  have literalStart : (applyPaidDrain S l start).val = filledInner l j.val := by
    rw [exact_OriginalPaidDrainLiteral,startValue]
    change filledDrain l (applied (level l) j.val (actualArg S l).val (paidOperand S l).val) =
      filledInner l j.val
    rw [actualArgLiteral,paidOperandLiteral] <;> rfl
  have alignedFirst : first = applyPaidDrain S l start :=
    Subtype.ext (firstValue.trans literalStart.symm)
  have alignedLast : finish = printedIndexedHead S l j := Subtype.ext finishValue
  have suffix : StrictRun S 3 (applyPaidDrain S l start) (applyPaidDrain S l finish) :=
    .cons inside₁.1 inside₁.2 (.cons inside₂.1 inside₂.2
      (.cons inside₃.1 inside₃.2 (.nil _)))
  rw [← alignedFirst,alignedLast] at suffix
  exact .cons firstRaw firstStrict suffix

/-- Actual map witness arises from the same original t_(l+2); it is not
provided by a separate semantic oracle. -/
theorem exact_ActualPrintedTowerAllInnerIndices (S : Signature) (l : Nat) :
    ∃ (mapping : ClosedNativeTerm S endo), mapping.val = innerMap l ∧
      ∀ (j : ClosedNativeTerm S indexType),
        StrictRun S 4 (applyClosed mapping j) (applyPaidDrain S l (printedIndexedHead S l j)) := by
  obtain ⟨mapping,_,_,literal,_⟩ := exact_NativeTowerIndexedEntry S l
  exact ⟨mapping,literal,fun j => exact_OriginalInnerMapHigherIteratorRun S l mapping j literal⟩

#print axioms exact_OriginalPaidDrainLiteral
#print axioms exact_OriginalHigherIteratorEndpoint
#print axioms exact_OriginalInnerMapHigherIteratorRun
#print axioms exact_ActualPrintedTowerAllInnerIndices

end LogicLineages.PersistentMarking.NativeTowerInnerMapHigherIteratorProof
