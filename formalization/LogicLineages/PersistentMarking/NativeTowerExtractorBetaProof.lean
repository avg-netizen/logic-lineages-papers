import LogicLineages.PersistentMarking.NativeTowerExtractorTypingProof
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeTowerExtractorBetaProof
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeOrdinalBasisTargets NativeOrdinalBasisProof NativeOrdinalArithmeticTargets
open NativeOrdinalExponentialTargets NativeOrdinalExponentialTypingProof
open NativeTowerExtractorTargets NativeTowerExtractorTypingProof

private theorem unchanged {q τ} (h : Typed EmptyContext q τ) (value : Expr) (depth : Nat) :
    substitute (.cons value .nil) depth q = q :=
  (ClosedSyntaxProof.term EmptyContext depth (fun _ _ hx => by cases hx) q τ h 0
    (.cons value .nil)).2

private theorem substituteApp (value : Expr) (depth : Nat) (σ τ : Ty) (f a : Expr) :
    substitute (.cons value .nil) depth (app σ τ f a) =
      app σ τ (substitute (.cons value .nil) depth f) (substitute (.cons value .nil) depth a) := rfl

private theorem substitution (S : Signature) (h : ClosedNativeTerm S endo) :
    substitute (.cons h.val .nil) 0 zeroBody = zeroResult h.val := by
  have k : substitute (.cons h.val .nil) 1 (.bound endo 1) = h.val := by
    simp only [substitute,Nat.lt_irrefl,if_false,Nat.sub_self,Args.get,
      ClosedSyntaxProof.closedShift h.val endo h.property.1.1.1 1]
  have hi := (NativeIteratorChecks.exact_ClosedNativeIterator S .base).1.1.1
  unfold zeroBody zeroResult
  rw [substituteApp,unchanged (fixClosed S).1.1.1]
  change app endo endo ordinalFix (Expr.lam indexType
      (substitute (.cons h.val .nil) 1 zeroInner)) = _
  unfold zeroInner applied
  simp only [substituteApp,unchanged hi h.val 1,unchanged (zeroClosed S).1.1.1 h.val 1,k] <;> rfl

theorem nativeTowerExtractorZeroBeta : NativeTowerExtractorZeroBeta := by
  intro S h
  let code : ClosedNativeTerm S levelTwo := ⟨extractorZero,extractorZeroClosed S⟩
  obtain ⟨result,literal,step,strict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S endo endo zeroBody
      (extractorZeroClosed S) h
  exact ⟨applyClosed code h,result,rfl,literal.trans (substitution S h),step,strict⟩

#print axioms nativeTowerExtractorZeroBeta
end LogicLineages.PersistentMarking.NativeTowerExtractorBetaProof
