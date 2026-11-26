module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalStepLambdaTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalExponentialTypingProof
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedBetaChecks
public import LogicLineages.NativeModule.PersistentMarking.ClosedSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalStepLambdaProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeOrdinalBasisTargets
open NativeOrdinalArithmeticTargets NativeOrdinalArithmeticTypingProof NativeOrdinalExponentialTargets
open NativeOrdinalExponentialTypingProof NativeOrdinalStepLambdaTargets

private theorem rightStepClosed {S : Signature} (op : ClosedNativeTerm S binaryType)
    (a : ClosedNativeTerm S indexType) :
    ClosedNative S (.lam indexType (binaryApplication op.val (.bound indexType 0) a.val)) endo := by
  let Γ := EmptyContext.push indexType
  have fnTyped := ClosingProof.weakening op.val binaryType op.property.1.1.1 Γ
  have rightTyped := ClosingProof.weakening a.val indexType a.property.1.1.1 Γ
  have bodyTyped : Typed Γ (binaryApplication op.val (.bound indexType 0) a.val) indexType :=
    .head (.cons (.head (.cons fnTyped (.cons (.bound rfl) .nil))) (.cons rightTyped .nil))
  have innerValid : Valid S (app indexType endo op.val (.bound indexType 0)) :=
    ⟨⟨0, rfl⟩, op.property.1.1.2, True.intro, True.intro⟩
  have bodyValid : Valid S (binaryApplication op.val (.bound indexType 0) a.val) :=
    ⟨⟨0, rfl⟩, innerValid, a.property.1.1.2, True.intro⟩
  have bodyOrdinary : Ordinary (binaryApplication op.val (.bound indexType 0) a.val) :=
    ⟨⟨op.property.1.2.1, True.intro, True.intro⟩, a.property.1.2.1, True.intro⟩
  refine ⟨⟨⟨.lam bodyTyped, bodyValid⟩, bodyOrdinary, ?_⟩, ?_⟩
  · intro n
    simp [binaryApplication, app, freeOccurs, freeOccursArgs, op.property.1.2.2 n, a.property.1.2.2 n]
  · intro n k
    simp [binaryApplication, app, DecisionInventory.heads, DecisionInventory.headsArgs,
      op.property.2 n k, a.property.2 n k]

theorem multiplicationStepClosed (S : Signature) (a : ClosedNativeTerm S indexType) :
    ClosedNative S (multiplicationStep a.val) endo :=
  rightStepClosed ⟨addition, additionClosed S⟩ a

private theorem rightOperandBeta {S : Signature} (op : ClosedNativeTerm S binaryType)
    (a x : ClosedNativeTerm S indexType) :
    StepLambdaBeta S (.lam indexType (binaryApplication op.val (.bound indexType 0) a.val))
      (binaryApplication op.val x.val a.val) x := by
  let body := binaryApplication op.val (.bound indexType 0) a.val
  have functionTyped := rightStepClosed op a
  obtain ⟨target, literal, reduction, edge⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S indexType indexType body functionTyped x
  have eqBody : substitute (.cons x.val .nil) 0 body = binaryApplication op.val x.val a.val := by
    let values := Args.cons x.val .nil
    change binaryApplication (substitute values 0 op.val)
      (substitute values 0 (.bound indexType 0)) (substitute values 0 a.val) =
        binaryApplication op.val x.val a.val
    rw [ClosedSyntaxProof.closedSubstitute op.val binaryType op.property.1.1.1 values,
      ClosedSyntaxProof.closedSubstitute a.val indexType a.property.1.1.1 values]
    simp only [values, substitute, Nat.lt_irrefl, if_false, Nat.sub_zero, Args.get, SubstitutionProof.shiftZero]
  exact ⟨applyClosed ⟨.lam indexType body, functionTyped⟩ x, target, rfl, literal.trans eqBody, reduction, edge⟩

theorem multiplicationStepBeta : MultiplicationStepLambdaBeta := by
  intro S a x
  exact rightOperandBeta ⟨addition, additionClosed S⟩ a x

theorem powerStepBeta : PowerStepLambdaBeta := by
  intro S x
  exact rightOperandBeta ⟨multiplication, multiplicationClosed S⟩ ⟨omegaCarrier, omegaClosed S⟩ x

end LogicLineages.PersistentMarking.NativeOrdinalStepLambdaProof
