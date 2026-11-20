import LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.NativeClosedApplicationChecks
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeOrdinalExponentialTransportProof
open Spine NativeReduction StructuralContext NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeClosedApplication NativeOrdinalBasisTargets
open NativeOrdinalBasisProof NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeOrdinalExponentialTypingProof

private theorem unchanged {q τ} (h : Typed EmptyContext q τ) (value : Expr) (depth : Nat) :
    substitute (.cons value .nil) depth q = q :=
  (ClosedSyntaxProof.term EmptyContext depth (fun _ _ hx => by cases hx) q τ h 0
    (.cons value .nil)).2

private theorem substituteApp (value : Expr) (depth : Nat) (σ τ : Ty) (f a : Expr) :
    substitute (.cons value .nil) depth (app σ τ f a) =
      app σ τ (substitute (.cons value .nil) depth f) (substitute (.cons value .nil) depth a) := rfl

private theorem substituteIterator (S : Signature) (v : Expr) (depth : Nat) (n f z : Expr) :
    substitute (.cons v .nil) depth (applied .base n f z) =
      applied .base (substitute (.cons v .nil) depth n)
        (substitute (.cons v .nil) depth f) (substitute (.cons v .nil) depth z) := by
  have typing := (NativeIteratorChecks.exact_ClosedNativeIterator S .base).1.1.1
  simp only [applied, substituteApp, unchanged typing v depth]

private theorem atSlot {S τ} (a : ClosedNativeTerm S τ) (depth : Nat) :
    substitute (.cons a.val .nil) depth (.bound τ depth) = a.val := by
  simp only [substitute, Nat.lt_irrefl, if_false, Nat.sub_self, Args.get,
    ClosedSyntaxProof.closedShift a.val τ a.property.1.1.1 depth]

private theorem powerSubstitution (S : Signature) (a : ClosedNativeTerm S indexType) :
    substitute (.cons a.val .nil) 0 powerBody = powerResult a.val := by
  unfold powerBody powerResult
  rw [substituteIterator S, atSlot a 0, unchanged (powerStepClosed S).1.1.1 a.val 0,
    unchanged (oneClosed S).1.1.1 a.val 0]

private theorem fixFirst (S : Signature) (f : ClosedNativeTerm S endo) :
    substitute (.cons f.val .nil) 0 fixBody = .lam indexType (fixAfterFunction f.val) := by
  let seed := app indexType indexType ordinalSuccessor (.bound indexType 0)
  have seedUnchanged : substitute (.cons f.val .nil) 1 seed = seed := by
    unfold seed
    rw [substituteApp, unchanged (successorClosed S).1.1.1 f.val 1] <;> rfl
  change Expr.lam indexType
      (substitute (.cons f.val .nil) 1 (applied .base omegaCarrier (.bound endo 1) seed)) =
      Expr.lam indexType (fixAfterFunction f.val)
  apply congrArg (Expr.lam indexType)
  rw [substituteIterator S, unchanged (omegaClosed S).1.1.1 f.val 1,
    atSlot f 1, seedUnchanged] <;> rfl

private theorem fixLast (S : Signature) (f : ClosedNativeTerm S endo) (z : ClosedNativeTerm S indexType) :
    substitute (.cons z.val .nil) 0 (fixAfterFunction f.val) = fixResult f.val z.val := by
  unfold fixAfterFunction fixResult
  rw [substituteIterator S, unchanged (omegaClosed S).1.1.1 z.val 0,
    unchanged f.property.1.1.1 z.val 0, substituteApp,
    unchanged (successorClosed S).1.1.1 z.val 0, atSlot z 0]

theorem powerBeta : NativeOrdinalPowerBeta := by
  intro S a
  have typing := powerClosed S
  obtain ⟨result, literal, raw, strict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S indexType indexType powerBody typing a
  exact ⟨applyClosed ⟨ordinalPower, typing⟩ a, result, rfl,
    literal.trans (powerSubstitution S a), raw, strict⟩

theorem fixBeta : NativeOrdinalFixBeta := by
  intro S f z
  let operation : ClosedNativeTerm S (.arrow endo endo) := ⟨ordinalFix, fixClosed S⟩
  let firstApplication := applyClosed operation f
  obtain ⟨firstResult, firstValue, firstRaw, firstStrict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S endo endo fixBody (fixClosed S) f
  have functionLiteral := firstValue.trans (fixFirst S f)
  have functionTyped : ClosedNative S (.lam indexType (fixAfterFunction f.val)) endo := by
    rw [← functionLiteral]
    exact firstResult.property
  obtain ⟨result, resultValue, secondRaw, secondStrict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S indexType indexType (fixAfterFunction f.val) functionTyped z
  let start := applyClosed firstApplication z
  let middle := applyClosed firstResult z
  let C : Context := .head (.app indexType indexType) .nil .hole (.cons z.val .nil)
  have contextTyped : ContextTyped S C endo indexType :=
    .head .hole ⟨0, rfl⟩ .nil True.intro True.intro (.cons z.property.1.1.1 .nil)
      ⟨z.property.1.1.2, True.intro⟩ ⟨z.property.1.2.1, True.intro⟩ rfl
  have firstInContext : Reduction S start.val middle.val := by
    change Reduction S (fill C firstApplication.val) (fill C firstResult.val)
    exact .context contextTyped firstApplication.property.1.1 firstResult.property.1.1 firstRaw
  have functionEq : firstResult = (⟨.lam indexType (fixAfterFunction f.val), functionTyped⟩ :
      ClosedNativeTerm S endo) := Subtype.ext functionLiteral
  have middleEq : middle = applyClosed ⟨.lam indexType (fixAfterFunction f.val), functionTyped⟩ z :=
    congrArg (fun q => applyClosed q z) functionEq
  have secondAtRoot : Reduction S middle.val result.val := by
    rw [middleEq]
    exact secondRaw
  have firstEdge : NativeBelow middle start :=
    NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S indexType indexType
      firstApplication firstResult z firstStrict
  have secondEdge : NativeBelow result middle := by
    rw [middleEq]
    exact secondStrict
  refine ⟨start, middle, result, rfl, ?_, resultValue.trans (fixLast S f z),
    firstInContext, secondAtRoot, firstEdge, secondEdge⟩
  change app indexType indexType firstResult.val z.val =
    app indexType indexType (.lam indexType (fixAfterFunction f.val)) z.val
  rw [functionLiteral]

theorem nextBeta : NativeOrdinalNextBeta := by
  intro S z
  exact fixBeta S ⟨ordinalPower, powerClosed S⟩ z

end LogicLineages.PersistentMarking.NativeOrdinalExponentialTransportProof
