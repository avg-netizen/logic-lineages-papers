module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalBasisProof
public import LogicLineages.NativeModule.PersistentMarking.NativeIteratorChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticTypingProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets

private structure NativeIn (S : Signature) (C : BoundContext) (q : Expr) (τ : Ty) : Prop where
  typed : Typed C q τ
  valid : Valid S q
  ordinary : Ordinary q
  closed : Closed q
  native : Native q

private theorem closedIn {S q τ} (C : BoundContext) (h : ClosedNative S q τ) : NativeIn S C q τ :=
  ⟨ClosingProof.weakening q τ h.1.1.1 C, h.1.1.2, h.1.2.1, h.1.2.2, h.2⟩

private theorem close {S q τ} (h : NativeIn S EmptyContext q τ) : ClosedNative S q τ :=
  ⟨⟨⟨h.typed, h.valid⟩, h.ordinary, h.closed⟩, h.native⟩

private theorem boundIn (S : Signature) (C : BoundContext) (σ : Ty) (k : Nat)
    (h : C k = some σ) : NativeIn S C (.bound σ k) σ :=
  ⟨.bound h, True.intro, True.intro, fun _ => rfl, fun _ _ => by simp [DecisionInventory.heads]⟩

private theorem appIn {S C σ τ f a}
    (hf : NativeIn S C f (.arrow σ τ)) (ha : NativeIn S C a σ) :
    NativeIn S C (app σ τ f a) τ where
  typed := .head (.cons hf.typed (.cons ha.typed .nil))
  valid := ⟨⟨0, rfl⟩, hf.valid, ha.valid, True.intro⟩
  ordinary := ⟨hf.ordinary, ha.ordinary, True.intro⟩
  closed := fun name => by simp [app, freeOccurs, freeOccursArgs, hf.closed name, ha.closed name]
  native := fun name arity => by
    simp [app, DecisionInventory.heads, DecisionInventory.headsArgs, hf.native name arity, ha.native name arity]

private theorem lamIn {S C σ τ body} (h : NativeIn S (C.push σ) body τ) :
    NativeIn S C (.lam σ body) (.arrow σ τ) :=
  ⟨.lam h.typed, h.valid, h.ordinary, h.closed, h.native⟩

private theorem iteratorIn {S C i p u} (hi : NativeIn S C i indexType)
    (hp : NativeIn S C p endo) (hu : NativeIn S C u indexType) :
    NativeIn S C (applied .base i p u) indexType :=
  appIn (appIn (appIn (closedIn C (NativeIteratorChecks.exact_ClosedNativeIterator S .base)) hi) hp) hu

theorem additionClosed (S : Signature) : ClosedNative S addition binaryType := by
  let C := (EmptyContext.push indexType).push indexType
  have body := iteratorIn (boundIn S C indexType 0 rfl)
    (closedIn C (NativeOrdinalBasisProof.successorClosed S)) (boundIn S C indexType 1 rfl)
  exact close (lamIn (lamIn body))

theorem multiplicationClosed (S : Signature) : ClosedNative S multiplication binaryType := by
  let C := (EmptyContext.push indexType).push indexType
  let inside := C.push indexType
  have stepBody : NativeIn S inside
      (binaryApplication addition (.bound indexType 0) (.bound indexType 2)) indexType :=
    appIn (appIn (closedIn inside (additionClosed S)) (boundIn S inside indexType 0 rfl))
      (boundIn S inside indexType 2 rfl)
  have body := iteratorIn (boundIn S C indexType 0 rfl) (lamIn stepBody)
    (closedIn C (NativeOrdinalBasisProof.zeroClosed S))
  exact close (lamIn (lamIn body))

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticTypingProof
