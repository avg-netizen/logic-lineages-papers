module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticSubstitutionProof
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedBetaChecks
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedApplicationChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticTransportProof
open Spine NativeReduction StructuralContext NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeOrdinalArithmeticTargets
open NativeOrdinalArithmeticTypingProof NativeOrdinalArithmeticSubstitutionProof

private theorem transport (body : Expr) (afterFirst : Expr → Expr) (result : Expr → Expr → Expr)
    (typed : ∀ S, ClosedNative S (.lam indexType body) binaryType)
    (firstEq : ∀ S (a : ClosedNativeTerm S indexType),
      substitute (.cons a.val .nil) 0 body = .lam indexType (afterFirst a.val))
    (secondEq : ∀ S (a b : ClosedNativeTerm S indexType),
      substitute (.cons b.val .nil) 0 (afterFirst a.val) = result a.val b.val) :
    BinaryOrdinalBeta (.lam indexType body) afterFirst result := by
  intro S a b
  let operator : ClosedNativeTerm S binaryType := ⟨.lam indexType body, typed S⟩
  let firstApplication := applyClosed operator a
  obtain ⟨firstResult, partialValue, firstRaw, firstStrict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S indexType endo body (typed S) a
  have partialLiteral := partialValue.trans (firstEq S a)
  have middleTyped : ClosedNative S (.lam indexType (afterFirst a.val)) endo := by
    rw [← partialLiteral]
    exact firstResult.property
  obtain ⟨final, finalValue, secondRaw, secondStrict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S indexType indexType (afterFirst a.val) middleTyped b

  let start := applyClosed firstApplication b
  let mid := applyClosed firstResult b
  let C : Context := .head (.app indexType indexType) .nil .hole (.cons b.val .nil)
  have contextTyped : ContextTyped S C endo indexType :=
    .head .hole ⟨0, rfl⟩ .nil True.intro True.intro (.cons b.property.1.1.1 .nil)
      ⟨b.property.1.1.2, True.intro⟩ ⟨b.property.1.2.1, True.intro⟩ rfl
  have firstInContext : Reduction S start.val mid.val := by
    change Reduction S (fill C firstApplication.val) (fill C firstResult.val)
    exact .context contextTyped firstApplication.property.1.1 firstResult.property.1.1 firstRaw
  have partialEq : firstResult = (⟨.lam indexType (afterFirst a.val), middleTyped⟩ :
      ClosedNativeTerm S endo) := Subtype.ext partialLiteral
  have midEq : mid = applyClosed ⟨.lam indexType (afterFirst a.val), middleTyped⟩ b :=
    congrArg (fun q => applyClosed q b) partialEq
  have secondAtRoot : Reduction S mid.val final.val := by
    rw [midEq]
    exact secondRaw
  have firstEdge : NativeBelow mid start :=
    NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S indexType indexType
      firstApplication firstResult b firstStrict
  have secondEdge : NativeBelow final mid := by
    rw [midEq]
    exact secondStrict

  refine ⟨start, mid, final, ?_, ?_, finalValue.trans (secondEq S a b),
    firstInContext, secondAtRoot, firstEdge, secondEdge⟩
  · rfl
  · change app indexType indexType firstResult.val b.val =
      app indexType indexType (.lam indexType (afterFirst a.val)) b.val
    rw [partialLiteral]

theorem additionBeta : OrdinalAdditionBeta :=
  transport additionBody additionAfterFirst additionResult additionClosed additionFirst additionLast

theorem multiplicationBeta : OrdinalMultiplicationBeta :=
  transport multiplicationBody multiplicationAfterFirst multiplicationResult
    multiplicationClosed multiplicationFirst multiplicationLast

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticTransportProof
