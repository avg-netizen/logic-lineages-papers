module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalExponentialTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeOrdinalBasisTargets NativeOrdinalBasisProof
open NativeOrdinalArithmeticTargets NativeOrdinalArithmeticTypingProof NativeOrdinalExponentialTargets

private structure OpenNative (S : Signature) (Γ : BoundContext) (q : Expr) (τ : Ty) : Prop where
  typing : Typed Γ q τ
  validity : Valid S q
  ordinary : Ordinary q
  freeClosed : Closed q
  native : Native q

private theorem ofClosed {S q τ} (Γ : BoundContext) (h : ClosedNative S q τ) : OpenNative S Γ q τ :=
  ⟨ClosingProof.weakening q τ h.1.1.1 Γ, h.1.1.2, h.1.2.1, h.1.2.2, h.2⟩

private theorem closed {S q τ} (h : OpenNative S EmptyContext q τ) : ClosedNative S q τ :=
  ⟨⟨⟨h.typing, h.validity⟩, h.ordinary, h.freeClosed⟩, h.native⟩

private theorem bound {S Γ τ i} (h : Γ i = some τ) : OpenNative S Γ (.bound τ i) τ :=
  ⟨.bound h, True.intro, True.intro, fun _ => rfl, fun _ _ => by simp [DecisionInventory.heads]⟩

private theorem application {S Γ σ τ f a}
    (hf : OpenNative S Γ f (.arrow σ τ)) (ha : OpenNative S Γ a σ) :
    OpenNative S Γ (app σ τ f a) τ where
  typing := .head (.cons hf.typing (.cons ha.typing .nil))
  validity := ⟨⟨0, rfl⟩, hf.validity, ha.validity, True.intro⟩
  ordinary := ⟨hf.ordinary, ha.ordinary, True.intro⟩
  freeClosed := fun n => by simp [app, freeOccurs, freeOccursArgs, hf.freeClosed n, ha.freeClosed n]
  native := fun n k => by
    simp [app, DecisionInventory.heads, DecisionInventory.headsArgs, hf.native n k, ha.native n k]

private theorem abstraction {S Γ σ τ body} (h : OpenNative S (Γ.push σ) body τ) :
    OpenNative S Γ (.lam σ body) (.arrow σ τ) :=
  ⟨.lam h.typing, h.validity, h.ordinary, h.freeClosed, h.native⟩

private theorem iteration {S Γ n f z}
    (hn : OpenNative S Γ n indexType) (hf : OpenNative S Γ f endo)
    (hz : OpenNative S Γ z indexType) : OpenNative S Γ (applied .base n f z) indexType :=
  application (application (application
    (ofClosed Γ (NativeIteratorChecks.exact_ClosedNativeIterator S .base)) hn) hf) hz

theorem oneClosed (S : Signature) : ClosedNative S ordinalOne indexType :=
  NativeClosedProof.application S indexType indexType ordinalSuccessor ordinalZero
    (successorClosed S) (zeroClosed S)

theorem omegaClosed (S : Signature) : ClosedNative S omegaCarrier indexType :=
  (closedBasis S).2.2

theorem powerStepClosed (S : Signature) : ClosedNative S powerStep endo := by
  let Γ := EmptyContext.push indexType
  have x : OpenNative S Γ (.bound indexType 0) indexType := bound rfl
  have body := application (application (ofClosed Γ (multiplicationClosed S)) x)
    (ofClosed Γ (omegaClosed S))
  exact closed (abstraction body)

theorem powerClosed (S : Signature) : ClosedNative S ordinalPower endo := by
  let Γ := EmptyContext.push indexType
  have a : OpenNative S Γ (.bound indexType 0) indexType := bound rfl
  exact closed (abstraction (iteration a (ofClosed Γ (powerStepClosed S)) (ofClosed Γ (oneClosed S))))

theorem fixClosed (S : Signature) : ClosedNative S ordinalFix (.arrow endo endo) := by
  let Γ := (EmptyContext.push endo).push indexType
  have f : OpenNative S Γ (.bound endo 1) endo := bound rfl
  have z : OpenNative S Γ (.bound indexType 0) indexType := bound rfl
  have seed := application (ofClosed Γ (successorClosed S)) z
  exact closed (abstraction (abstraction (iteration (ofClosed Γ (omegaClosed S)) f seed)))

theorem nextClosed (S : Signature) : ClosedNative S ordinalNext endo :=
  NativeClosedProof.application S endo endo ordinalFix ordinalPower (fixClosed S) (powerClosed S)

end LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof
