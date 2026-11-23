import LogicLineages.PersistentMarking.NativeTowerEraseCodeKernel
import LogicLineages.PersistentMarking.NativeTowerTypeCodeBridge
import LogicLineages.PersistentMarking.NativeTowerNumericCodeTargets
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof

namespace LogicLineages.PersistentMarking.NativeTowerEraseCodeBridge
open Spine NativeIteratorTargets NativeIndexedCarrierTargets NativeTowerWitnessPrefixTargets
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerTypeCodeBridge (exactNativeTowerTypeCode)
open NativeTowerEraseCodeKernel (fields2 code2 boundCode lambdaCode wrap eraseCode)
open NativeTowerNumericCodeTargets (rawCode)
open NumberedWindowArithmeticFields (encodeFields encodeNode)
open NumberedWindowArithmeticTyCode (encodeTy)

theorem exactCode2 (tag a b : Nat) : code2 tag a b = encodeNode tag [a,b] := rfl

theorem exactBoundCode (τ : Ty) (slot : Nat) :
    boundCode (encodeTy τ) slot = rawCode (.bound τ slot) := rfl

theorem exactLambdaCode (τ : Ty) {q : Expr} (original : Ordinary q) :
    lambdaCode (encodeTy τ) (rawCode q) = rawCode (.lam τ q) := by
  obtain ⟨Q,hQ⟩ := (NumberedWindowOrdinaryDomainProof.termDomain q).mpr original
  simp only [rawCode,NumberedWindowOrdinaryTranslation.tr,hQ,Option.map_some,Option.getD_some]
  rfl

private theorem erasureOrdinary (n : Nat) (slot : Nat) : Ordinary (eraseBound (level n) slot) := by
  induction n generalizing slot with
  | zero => trivial
  | succ n ih =>
    change Ordinary (eraseBound (level n) (slot+1))
    exact ih (slot+1)

theorem exactEraseCode (n slot : Nat) :
    eraseCode n slot = rawCode (eraseBound (level n) slot) := by
  induction n generalizing slot with
  | zero => rfl
  | succ n ih =>
    have inner : wrap n (boundCode (typeCode 0) (slot+(n+1))) =
        eraseCode n (slot+1) := by
      unfold eraseCode
      rw [show slot+(n+1) = slot+1+n by omega]
    change lambdaCode (typeCode n) (wrap n (boundCode (typeCode 0) (slot+(n+1)))) =
      rawCode (.lam (ty n) (eraseBound (level n) (slot+1)))
    rw [inner,ih,exactNativeTowerTypeCode,exactLambdaCode _ (erasureOrdinary n (slot+1))]

#print axioms exactCode2
#print axioms exactBoundCode
#print axioms exactLambdaCode
#print axioms exactEraseCode
end LogicLineages.PersistentMarking.NativeTowerEraseCodeBridge
