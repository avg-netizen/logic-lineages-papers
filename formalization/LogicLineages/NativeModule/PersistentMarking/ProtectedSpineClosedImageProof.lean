module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineTableProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineScopeAgreementProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineFreeInputProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineClosedImageProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineAgreementTargets
open ProtectedSpineVariableProof (lookupEvaluation)
open MarkedConstructorTargets (PrefixClosed)

theorem image (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (r : Expr) (σ : Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hty : Typed EmptyContext r σ) (hcov : Covered E H r)
    (get : Context → Assignments → Code) (blocked : Nat → Bool)
    (R : FrameRelation) (P : Nat → Nat → Prop)
    (hcode : ∀ Γ a b, R Γ a b → get Γ a = codeAt E σ (evaluate S E H M r) Γ ⟨b.free,[]⟩)
    (hunblocked : ∀ k l, P k l → blocked k = false) :
    Agreement E σ (lookupEvaluation E σ get blocked) (evaluate S E H M r) R P := by
  let ev := evaluate S E H M r
  have hl := ProtectedSpineInterpretationProof.laws S E H M hc hm EmptyContext r σ hty hcov
  have hag := ProtectedSpineScopeAgreementProof.exact_ScopeAgreement S E H M EmptyContext r σ hty hcov
  have hs : ∀ Γ b, SameInputs E EmptyContext Γ ⟨b.free,[]⟩ b :=
    fun _ _ => ⟨fun _ _ => rfl,fun _ _ h => by cases h⟩
  constructor
  · intro Γ a b ha hb hr
    let b₀ : Assignments := ⟨b.free,[]⟩
    have hb₀ := ProtectedSpineFreeInputProof.emptyBoundValid E Γ b hb
    change ValueEq E σ Γ (decode E σ Γ (get Γ a)) (valueAt ev Γ b)
    rw [hcode Γ a b hr]
    exact HereditaryValueEqualityProof.trans (ProtectedSpineEncodingProof.encodeAt E σ ev hl Γ b₀ hb₀).2
      (hag.value Γ b₀ b hb₀ hb (hs Γ b))
  · intro Γ a b k l ds τ xs ha hb hr hkl hp hx
    let b₀ : Assignments := ⟨b.free,[]⟩
    have hb₀ := ProtectedSpineFreeInputProof.emptyBoundValid E Γ b hb
    rw [ProtectedSpineVariableProof.callEq E σ get blocked Γ a k ds τ xs hp hx,hunblocked k l hkl]
    change StructuralActions.fullAction E σ Γ (get Γ a) ds τ xs = _
    rw [hcode Γ a b hr]
    have hv := (ProtectedSpineEncodingProof.encodeAt E σ ev hl Γ b₀ hb₀).2
    have hApp := (hv Γ hb.1 (DecisionPortsProof.extensionRefl Γ)).2.2 ds τ hp xs hx
    have hTable := ProtectedSpineTableProof.table S E H M EmptyContext r σ hc hm hty hcov Γ b₀ hb₀ ds τ xs hp hx
    have hAg := hag.call Γ b₀ b 0 l ds τ xs hb₀ hb (hs Γ b) (by intro _ _ h; cases h) hp hx
    exact hApp.trans (hTable.symm.trans hAg)

end LogicLineages.PersistentMarking.ProtectedSpineClosedImageProof
