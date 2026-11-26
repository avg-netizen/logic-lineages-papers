module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticTypingProof
public import LogicLineages.NativeModule.PersistentMarking.ClosedSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticSubstitutionProof
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorTargets
open NativeIteratorStrictTargets NativeOrdinalBasisTargets NativeOrdinalBasisProof
open NativeOrdinalArithmeticTargets NativeOrdinalArithmeticTypingProof

private theorem unchanged {q τ} (h : Typed EmptyContext q τ) (values : Args) (depth : Nat) :
    substitute values depth q = q :=
  (ClosedSyntaxProof.term EmptyContext depth (fun _ _ hx => by cases hx) q τ h 0 values).2

private theorem substituteApp (values : Args) (depth : Nat) (σ τ : Ty) (q a : Expr) :
    substitute values depth (app σ τ q a) =
      app σ τ (substitute values depth q) (substitute values depth a) := rfl

private theorem substituteCall (S : Signature) (values : Args) (depth : Nat) (i p u : Expr) :
    substitute values depth (applied .base i p u) =
      applied .base (substitute values depth i) (substitute values depth p) (substitute values depth u) := by
  have original := (NativeIteratorChecks.exact_ClosedNativeIterator S .base).1.1.1
  simp only [applied, substituteApp, unchanged original values depth]

private theorem nearer (a : Expr) (i depth : Nat) (h : i < depth) :
    substitute (.cons a .nil) depth (.bound indexType i) = .bound indexType i := by
  simp only [substitute, h, if_true]

private theorem atSlot {S} (a : ClosedNativeTerm S indexType) (depth : Nat) :
    substitute (.cons a.val .nil) depth (.bound indexType depth) = a.val := by
  simp only [substitute, Nat.lt_irrefl, if_false, Nat.sub_self, Args.get,
    ClosedSyntaxProof.closedShift a.val indexType a.property.1.1.1 depth]

theorem additionFirst (S : Signature) (a : ClosedNativeTerm S indexType) :
    substitute (.cons a.val .nil) 0 additionBody = .lam indexType (additionAfterFirst a.val) := by
  change Expr.lam indexType (substitute (.cons a.val .nil) 1
    (applied .base (.bound indexType 0) ordinalSuccessor (.bound indexType 1))) =
      Expr.lam indexType (additionAfterFirst a.val)
  apply congrArg (Expr.lam indexType)
  rw [substituteCall S, nearer a.val 0 1 (by decide),
    unchanged (successorClosed S).1.1.1 (.cons a.val .nil) 1, atSlot a 1] <;> rfl

theorem additionLast (S : Signature) (a b : ClosedNativeTerm S indexType) :
    substitute (.cons b.val .nil) 0 (additionAfterFirst a.val) = additionResult a.val b.val := by
  unfold additionAfterFirst additionResult
  rw [substituteCall S, atSlot b 0, unchanged (successorClosed S).1.1.1 (.cons b.val .nil) 0,
    unchanged a.property.1.1.1 (.cons b.val .nil) 0]

theorem multiplicationFirst (S : Signature) (a : ClosedNativeTerm S indexType) :
    substitute (.cons a.val .nil) 0 multiplicationBody =
      .lam indexType (multiplicationAfterFirst a.val) := by
  let step := Expr.lam indexType (binaryApplication addition (.bound indexType 0) (.bound indexType 2))
  have mappedStep : substitute (.cons a.val .nil) 1 step = multiplicationStep a.val := by
    change Expr.lam indexType (substitute (.cons a.val .nil) 2
      (binaryApplication addition (.bound indexType 0) (.bound indexType 2))) = multiplicationStep a.val
    apply congrArg (Expr.lam indexType)
    simp only [multiplicationStep, binaryApplication, substituteApp,
      unchanged (additionClosed S).1.1.1 (.cons a.val .nil) 2,
      nearer a.val 0 2 (by decide), atSlot a 2]
  change Expr.lam indexType (substitute (.cons a.val .nil) 1
    (applied .base (.bound indexType 0) step ordinalZero)) =
      Expr.lam indexType (multiplicationAfterFirst a.val)
  apply congrArg (Expr.lam indexType)
  rw [substituteCall S, nearer a.val 0 1 (by decide), mappedStep,
    unchanged (zeroClosed S).1.1.1 (.cons a.val .nil) 1] <;> rfl

theorem multiplicationLast (S : Signature) (a b : ClosedNativeTerm S indexType) :
    substitute (.cons b.val .nil) 0 (multiplicationAfterFirst a.val) =
      multiplicationResult a.val b.val := by
  have unchangedStep :
      substitute (.cons b.val .nil) 0 (multiplicationStep a.val) = multiplicationStep a.val := by
    change Expr.lam indexType (substitute (.cons b.val .nil) 1
      (binaryApplication addition (.bound indexType 0) a.val)) = multiplicationStep a.val
    apply congrArg (Expr.lam indexType)
    simp only [multiplicationStep, binaryApplication, substituteApp,
      unchanged (additionClosed S).1.1.1 (.cons b.val .nil) 1,
      nearer b.val 0 1 (by decide), unchanged a.property.1.1.1 (.cons b.val .nil) 1]
  unfold multiplicationAfterFirst multiplicationResult
  rw [substituteCall S, atSlot b 0, unchangedStep, unchanged (zeroClosed S).1.1.1 (.cons b.val .nil) 0]

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticSubstitutionProof
