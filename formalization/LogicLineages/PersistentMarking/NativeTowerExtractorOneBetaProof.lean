import LogicLineages.PersistentMarking.NativeTowerExtractorOneBetaTargets
import LogicLineages.PersistentMarking.NativeTowerExtractorTypingProof
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.NativeClosedApplicationChecks
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeTowerExtractorOneBetaProof
open Spine NativeReduction StructuralContext NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeOrdinalBasisTargets NativeOrdinalBasisProof NativeOrdinalArithmeticTargets
open NativeOrdinalExponentialTargets NativeOrdinalExponentialTypingProof
open NativeTowerExtractorTargets NativeTowerExtractorTypingProof NativeTowerExtractorOneBetaTargets

private theorem unchanged {q τ} (h : Typed EmptyContext q τ) (value : Expr) (depth : Nat) :
    substitute (.cons value .nil) depth q = q :=
  (ClosedSyntaxProof.term EmptyContext depth (fun _ _ hx => by cases hx) q τ h 0
    (.cons value .nil)).2

private theorem substituteApp (value : Expr) (depth : Nat) (σ τ : Ty) (f a : Expr) :
    substitute (.cons value .nil) depth (app σ τ f a) =
      app σ τ (substitute (.cons value .nil) depth f) (substitute (.cons value .nil) depth a) := rfl

private theorem substituteIterator (S : Signature) (v : Expr) (d : Nat) (n f z : Expr) :
    substitute (.cons v .nil) d (applied levelOne n f z) =
      applied levelOne (substitute (.cons v .nil) d n)
        (substitute (.cons v .nil) d f) (substitute (.cons v .nil) d z) := by
  have hp := (NativeIteratorChecks.exact_ClosedNativeIterator S levelOne).1.1.1
  simp only [applied,substituteApp,unchanged hp v d]

private theorem atSlot {S τ} (h : ClosedNativeTerm S τ) (d : Nat) :
    substitute (.cons h.val .nil) d (.bound τ d) = h.val := by
  simp only [substitute,Nat.lt_irrefl,if_false,Nat.sub_self,Args.get,
    ClosedSyntaxProof.closedShift h.val τ h.property.1.1.1 d]

private theorem substituteFirst (S : Signature) (h : ClosedNativeTerm S levelTwo) :
    substitute (.cons h.val .nil) 0 (.lam endo oneBody) =
      .lam endo (oneAfterFunction h.val) := by
  change Expr.lam endo (substitute (.cons h.val .nil) 1 oneBody) = _
  apply congrArg (Expr.lam endo)
  unfold oneBody oneAfterFunction
  rw [substituteApp,unchanged (fixClosed S).1.1.1]
  change app endo endo ordinalFix (Expr.lam indexType
    (substitute (.cons h.val .nil) 2 oneInner)) = _
  unfold oneInner
  rw [substituteApp,substituteIterator S,atSlot h 2,unchanged (zeroClosed S).1.1.1] <;> rfl

private theorem substituteSecond (S : Signature) (h : ClosedNativeTerm S levelTwo)
    (h₁ : ClosedNativeTerm S endo) :
    substitute (.cons h₁.val .nil) 0 (oneAfterFunction h.val) = oneResult h.val h₁.val := by
  unfold oneAfterFunction oneResult
  rw [substituteApp,unchanged (fixClosed S).1.1.1]
  change app endo endo ordinalFix (.lam indexType
    (substitute (.cons h₁.val .nil) 1 (app indexType indexType
      (applied levelOne (.bound indexType 0) h.val (.bound endo 1)) ordinalZero))) = _
  rw [substituteApp,substituteIterator S,atSlot h₁ 1,unchanged h.property.1.1.1,
    unchanged (zeroClosed S).1.1.1] <;> rfl

theorem extractorOneOuterBeta : NativeExtractorOneOuterBeta := by
  intro S h
  let code : ClosedNativeTerm S levelThree := ⟨extractorOne,extractorOneClosed S⟩
  obtain ⟨result,literal,raw,strict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S levelTwo levelTwo (.lam endo oneBody)
      (extractorOneClosed S) h
  exact ⟨applyClosed code h,result,rfl,literal.trans (substituteFirst S h),raw,strict⟩

theorem extractorOneBeta : NativeExtractorOneBeta := by
  intro S h h₁
  obtain ⟨p,q,pVal,qVal,pqRaw,pqStrict⟩ := extractorOneOuterBeta S h
  have qTyped : ClosedNative S (.lam endo (oneAfterFunction h.val)) levelTwo := by
    rw [← qVal]
    exact q.property
  obtain ⟨r,rVal,qrRaw,qrStrict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S endo endo (oneAfterFunction h.val) qTyped h₁
  let start := applyClosed p h₁
  let middle := applyClosed q h₁
  let C : Context := .head (.app endo endo) .nil .hole (.cons h₁.val .nil)
  have contextTyped : ContextTyped S C levelTwo endo :=
    .head .hole ⟨0,rfl⟩ .nil True.intro True.intro (.cons h₁.property.1.1.1 .nil)
      ⟨h₁.property.1.1.2,True.intro⟩ ⟨h₁.property.1.2.1,True.intro⟩ rfl
  have firstRaw : Reduction S start.val middle.val := by
    change Reduction S (fill C p.val) (fill C q.val)
    exact .context contextTyped p.property.1.1 q.property.1.1 pqRaw
  have headEq : q = (⟨.lam endo (oneAfterFunction h.val),qTyped⟩ : ClosedNativeTerm S levelTwo) :=
    Subtype.ext qVal
  have middleEq : middle = applyClosed ⟨.lam endo (oneAfterFunction h.val),qTyped⟩ h₁ :=
    congrArg (fun x => applyClosed x h₁) headEq
  have secondRaw : Reduction S middle.val r.val := by
    rw [middleEq]
    exact qrRaw
  have firstStrict : NativeBelow middle start :=
    NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S endo endo p q h₁ pqStrict
  have secondStrict : NativeBelow r middle := by
    rw [middleEq]
    exact qrStrict
  refine ⟨start,middle,r,?_,?_,rVal.trans (substituteSecond S h h₁),
    firstRaw,secondRaw,firstStrict,secondStrict⟩
  · change app endo endo p.val h₁.val = _
    rw [pVal]
  · change app endo endo q.val h₁.val = _
    rw [qVal]

theorem nativeNBBeta : NativeNBBeta := by
  intro S
  exact extractorOneBeta S ⟨extractorZero,extractorZeroClosed S⟩ ⟨ordinalNext,nextClosed S⟩

#print axioms extractorOneOuterBeta
#print axioms extractorOneBeta
#print axioms nativeNBBeta
end LogicLineages.PersistentMarking.NativeTowerExtractorOneBetaProof
