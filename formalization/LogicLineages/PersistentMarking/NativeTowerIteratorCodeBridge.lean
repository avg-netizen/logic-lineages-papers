import LogicLineages.PersistentMarking.NativeTowerIteratorCodeKernel
import LogicLineages.PersistentMarking.NativeTowerEraseCodeBridge
import LogicLineages.PersistentMarking.NativeTowerNumericCodeApplicationProof

namespace LogicLineages.PersistentMarking.NativeTowerIteratorCodeBridge
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorTargets
open NativeTowerWitnessPrefixTargets
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerTypeCodeBridge (exactNativeTowerTypeCode)
open NativeTowerEraseCodeKernel (boundCode lambdaCode eraseCode)
open NativeTowerEraseCodeBridge (exactBoundCode exactLambdaCode exactEraseCode)
open NativeTowerIteratorCodeKernel
open NativeTowerNumericCodeTargets (rawCode ReadAt appCode)
open NativeTowerNumericCodeApplicationProof (readOrdinaryCode combineReads)
open NumberedWindowArithmeticTyCode (encodeTy)

theorem exactArrowCode (a b : Ty) :
    arrowCode (encodeTy a) (encodeTy b) = encodeTy (.arrow a b) := rfl

theorem exactApplicationCode (a b : Ty) (f x : Nat) :
    applicationCode (encodeTy a) (encodeTy b) f x = appCode a b f x := rfl

private theorem appOrdinary {a b : Ty} {f x : Expr} (hf : Ordinary f) (hx : Ordinary x) :
    Ordinary (app a b f x) := ⟨hf,hx,True.intro⟩

theorem exactRawApp (a b : Ty) {f x : Expr} (hf : Ordinary f) (hx : Ordinary x) :
    applicationCode (encodeTy a) (encodeTy b) (rawCode f) (rawCode x) = rawCode (app a b f x) := by
  rw [exactApplicationCode]
  obtain ⟨Q,hQ,hcode⟩ := combineReads a b f x _ _ (readOrdinaryCode f hf) (readOrdinaryCode x hx)
  simpa only [rawCode,hQ,Option.map_some,Option.getD_some] using hcode.symm

theorem exactZeroCode : zeroCode = rawCode zero := rfl
theorem exactRecHeadCode (a : Ty) :
    recHeadCode (encodeTy a) = rawCode (.head (.recursor a) .nil) := rfl

theorem exactRecursorCode (a : Ty) {z k u : Expr}
    (hz : Ordinary z) (hk : Ordinary k) (hu : Ordinary u) :
    recursorCode (encodeTy a) (rawCode z) (rawCode k) (rawCode u) =
      rawCode (recTerm a z k u) := by
  let endo := Ty.arrow a a
  let step := stepType a
  have recHead : Ordinary (.head (.recursor a) .nil) := True.intro
  have h₁ : Ordinary (rec1 a z) := appOrdinary recHead hz
  have h₂ : Ordinary (rec2 a z k) := appOrdinary h₁ hk
  unfold recursorCode
  change applicationCode (encodeTy a) (encodeTy a)
    (applicationCode (arrowCode 0 (arrowCode (encodeTy a) (encodeTy a)))
      (arrowCode (encodeTy a) (encodeTy a))
      (applicationCode 0
        (arrowCode (arrowCode 0 (arrowCode (encodeTy a) (encodeTy a)))
          (arrowCode (encodeTy a) (encodeTy a)))
        (recHeadCode (encodeTy a)) (rawCode z)) (rawCode k)) (rawCode u) = _
  simp only [show (0 : Nat) = encodeTy .ground by rfl,exactArrowCode,exactRecHeadCode]
  change applicationCode (encodeTy a) (encodeTy a)
    (applicationCode (encodeTy step) (encodeTy endo)
      (applicationCode (encodeTy .ground) (encodeTy (.arrow step endo))
        (rawCode (.head (.recursor a) .nil)) (rawCode z)) (rawCode k)) (rawCode u) = _
  rw [exactRawApp .ground (.arrow step endo) recHead hz]
  change applicationCode (encodeTy a) (encodeTy a)
      (applicationCode (encodeTy step) (encodeTy endo) (rawCode (rec1 a z)) (rawCode k)) (rawCode u) = _
  rw [exactRawApp step endo h₁ hk]
  exact exactRawApp a a h₂ hu

theorem exactDiscardCode (a : Ty) : discardCode (encodeTy a) = rawCode (discard a) := rfl

theorem exactLeftCode (a : Ty) {p : Expr} (hp : Ordinary p) :
    leftCode (encodeTy a) (rawCode p) = rawCode (left a p) := by
  unfold leftCode
  rw [exactArrowCode,exactDiscardCode]
  exact exactRawApp a (.arrow a a) (by trivial) hp

private theorem eraseOrdinary (n j : Nat) : Ordinary (eraseBound (level n) j) := by
  induction n generalizing j with
  | zero => trivial
  | succ n ih =>
    change Ordinary (eraseBound (level n) (j+1))
    exact ih (j+1)

theorem exactIteratorBodyCode (n : Nat) :
    iteratorBodyCode n = rawCode (iteratorBody (level n)) := by
  let a := ty n
  let e := ty (n+1)
  let p := Expr.bound e 2
  let erased := eraseBound (level (n+1)) 3
  let step := app e e (left e p) erased
  have hp : Ordinary p := True.intro
  have he := eraseOrdinary (n+1) 3
  have hl : Ordinary (left e p) := appOrdinary (by trivial) hp
  have hs : Ordinary step := appOrdinary hl he
  unfold iteratorBodyCode
  rw [exactNativeTowerTypeCode n,exactNativeTowerTypeCode (n+1)]
  change recursorCode (encodeTy a) zeroCode (lambdaCode 0
    (applicationCode (encodeTy e) (encodeTy e)
      (leftCode (encodeTy e) (boundCode (encodeTy e) 2))
      (eraseCode (n+1) 3))) (boundCode (encodeTy a) 0) = _
  rw [exactBoundCode e 2,exactBoundCode a 0,exactEraseCode,exactLeftCode e hp,exactRawApp e e hl he]
  change recursorCode (encodeTy a) zeroCode (lambdaCode 0 (rawCode step))
      (rawCode (.bound a 0)) = _
  rw [exactZeroCode,show (0 : Nat) = encodeTy .ground by rfl,exactLambdaCode _ hs]
  exact exactRecursorCode a (z := zero) (k := .lam .ground step) (u := .bound a 0)
    True.intro hs True.intro

theorem exactIteratorCode (S : Signature) (n : Nat) :
    iteratorCode n = rawCode (iterator (level n)) := by
  have h : Ordinary (iterator (level n)) :=
    (NativeIteratorChecks.exact_ClosedNativeIterator S (level n)).1.2.1
  change Ordinary (iteratorBody (level n)) at h
  unfold iteratorCode
  rw [exactNativeTowerTypeCode 0,exactNativeTowerTypeCode (n+1),exactNativeTowerTypeCode n,
    exactIteratorBodyCode,exactLambdaCode _ h]
  have h₁ : Ordinary (.lam (ty n) (iteratorBody (level n))) := h
  rw [exactLambdaCode _ h₁]
  have h₂ : Ordinary (.lam (ty (n+1)) (.lam (ty n) (iteratorBody (level n)))) := h
  exact exactLambdaCode _ h₂

#print axioms exactApplicationCode
#print axioms exactRecursorCode
#print axioms exactIteratorBodyCode
#print axioms exactIteratorCode
end LogicLineages.PersistentMarking.NativeTowerIteratorCodeBridge
