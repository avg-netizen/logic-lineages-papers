import LogicLineages.PersistentMarking.NativeTowerEffectiveCodeKernel
import LogicLineages.PersistentMarking.NativeTowerIteratorCodeBridge

namespace LogicLineages.PersistentMarking.NativeTowerEffectiveCodeSymbolicBridge
open Spine NativeIndexedCarrierTargets NativeOrdinalArithmeticTargets
open NativeTowerExtractorGeneralTargets NativeTowerWitnessPrefixTargets NativeTowerNumericCodeTargets
open NativeTowerTypeCodeBridge (exactNativeTowerTypeCode)
open NativeTowerIteratorCodeBridge (exactApplicationCode)
open NativeTowerExtractorCodeKernel (extractorCode)
open NativeTowerEffectiveCodeKernel

attribute [local irreducible] rawCode

theorem exactHomogeneous (j f x : Nat) :
    homogeneous j f x = appCode (ty j) (ty j) f x := by
  unfold homogeneous
  rw [exactNativeTowerTypeCode,exactApplicationCode]

theorem exactLower (fix : Nat) (extract : ∀ j, extractorCode fix j = rawCode (extractor j))
    (n head : Nat) : lower fix n head = lowerCode n head := by
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    unfold lower
    rw [List.range_succ,List.foldr_append]
    change lower fix n (lowerStep fix n head) = _
    rw [ih]
    unfold lowerStep
    rw [exactHomogeneous,extract] <;> rfl

theorem exactZero (c : Fixed) :
    NativeTowerEffectiveCodeKernel.zero c = appCode indexType indexType c.2.1 c.2.2 := by
  unfold NativeTowerEffectiveCodeKernel.zero
  exact exactHomogeneous 0 _ _

theorem exactOne (c : Fixed) :
    generate c 1 = appCode indexType indexType c.2.1
      (appCode indexType indexType c.2.1 c.2.2) := by
  change homogeneous 0 c.2.1 (NativeTowerEffectiveCodeKernel.zero c) = _
  rw [exactZero,exactHomogeneous 0] <;> rfl

theorem exactLater (c : Fixed)
    (extract : ∀ j, extractorCode c.1 j = rawCode (extractor j)) (j : Nat) :
    generate c (j+2) = appCode indexType indexType
      (appCode endo endo (lowerCode j (rawCode (extractor j))) c.2.1)
      (appCode indexType indexType c.2.1 c.2.2) := by
  change NativeTowerEffectiveCodeKernel.later c j = _
  unfold NativeTowerEffectiveCodeKernel.later
  rw [exactZero,exactHomogeneous 0,exactHomogeneous 1,exactLower c.1 extract,extract] <;> rfl

#print axioms exactLower
#print axioms exactLater
end LogicLineages.PersistentMarking.NativeTowerEffectiveCodeSymbolicBridge
