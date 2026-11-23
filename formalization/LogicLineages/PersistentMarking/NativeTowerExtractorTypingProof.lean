import LogicLineages.PersistentMarking.NativeTowerExtractorTargets
import LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof

namespace LogicLineages.PersistentMarking.NativeTowerExtractorTypingProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeOrdinalBasisTargets NativeOrdinalBasisProof
open NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeOrdinalExponentialTypingProof NativeTowerExtractorTargets

private structure OpenNative (S : Signature) (Γ : BoundContext) (q : Expr) (τ : Ty) : Prop where
  typing : Typed Γ q τ
  validity : Valid S q
  ordinary : Ordinary q
  freeClosed : Closed q
  native : Native q

private theorem ofClosed {S q τ} (Γ : BoundContext) (h : ClosedNative S q τ) : OpenNative S Γ q τ :=
  ⟨ClosingProof.weakening q τ h.1.1.1 Γ, h.1.1.2, h.1.2.1, h.1.2.2, h.2⟩

private theorem closeOpen {S q τ} (h : OpenNative S EmptyContext q τ) : ClosedNative S q τ :=
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

private theorem iteration {S Γ n f z} (A : SemanticType)
    (hn : OpenNative S Γ n indexType) (hf : OpenNative S Γ f (functionType A))
    (hz : OpenNative S Γ z (actualType A)) :
    OpenNative S Γ (applied A n f z) (actualType A) :=
  application (application (application
    (ofClosed Γ (NativeIteratorChecks.exact_ClosedNativeIterator S A)) hn) hf) hz

theorem extractorZeroClosed (S : Signature) : ClosedNative S extractorZero levelTwo := by
  let Γ := EmptyContext.push endo
  let Δ := Γ.push indexType
  have α : OpenNative S Δ (.bound indexType 0) indexType := bound rfl
  have h : OpenNative S Δ (.bound endo 1) endo := bound rfl
  have inside : OpenNative S Δ zeroInner indexType :=
    iteration .base α h (ofClosed Δ (zeroClosed S))
  have body : OpenNative S Γ zeroBody endo :=
    application (ofClosed Γ (fixClosed S)) (abstraction inside)
  exact closeOpen (abstraction body)

theorem extractorOneClosed (S : Signature) : ClosedNative S extractorOne levelThree := by
  let Γ := EmptyContext.push levelTwo
  let Δ := Γ.push endo
  let Θ := Δ.push indexType
  have α : OpenNative S Θ (.bound indexType 0) indexType := bound rfl
  have h : OpenNative S Θ (.bound levelTwo 2) (functionType levelOne) := bound rfl
  have h₁ : OpenNative S Θ (.bound endo 1) (actualType levelOne) := bound rfl
  have inside : OpenNative S Θ oneInner indexType :=
    application (iteration levelOne α h h₁) (ofClosed Θ (zeroClosed S))
  have body : OpenNative S Δ oneBody endo :=
    application (ofClosed Δ (fixClosed S)) (abstraction inside)
  exact closeOpen (abstraction (abstraction body))

theorem nativeNBClosed (S : Signature) : ClosedNative S nativeNB endo :=
  NativeClosedProof.application S endo endo
    (app levelTwo levelTwo extractorOne extractorZero) ordinalNext
    (NativeClosedProof.application S levelTwo levelTwo extractorOne extractorZero
      (extractorOneClosed S) (extractorZeroClosed S)) (nextClosed S)

theorem nativeTowerExtractorsClosed : ClosedNativeTowerExtractors :=
  fun S => ⟨extractorZeroClosed S,extractorOneClosed S,nativeNBClosed S⟩

#print axioms nativeTowerExtractorsClosed
end LogicLineages.PersistentMarking.NativeTowerExtractorTypingProof
