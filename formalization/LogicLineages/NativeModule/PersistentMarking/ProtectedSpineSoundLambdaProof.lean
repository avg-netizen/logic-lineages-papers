module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundLambdaCallProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundLambdaBitsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineInterpreterCore ProtectedSpineLaws
open ProtectedSpineSoundInterpreterTargets

theorem lambda (F : Inputs S) (M : Code) (α : Ty) (body : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ih : ExprGoal F M body) : ExprGoal F M (.lam α body) := by
  intro Γ types vs cs hTyped hu hw hf
  let E := domain F
  let H := F.data.sourceHeads
  let e := evaluate S E H M body
  let q := Expr.lam α body
  let a : Assignments := ⟨[],cs⟩
  have ht : Typed (BoundContext.prefix (α::types) EmptyContext) body body.type := by
    cases hTyped with
    | lam h => exact h
  have hBody := DecisionSourceBasicProof.lamChild _ _ _ _ _ _ hu
  have hLaws := ProtectedSpineInterpretationProof.laws S E H M (ProtectedSpineAdequacyBase.prefixClosed S F) hm
    _ q q.type hTyped
    (ProtectedSpineAdequacyBase.sourceCovered S F Γ q hu)
  have hEnc := ProtectedSpineEncodingProof.encodeAt E q.type (evaluate S E H M q) hLaws Γ a
    (ProtectedSpineSoundFrameProof.inputs F Γ types vs cs hw hf)
  constructor
  · rw [Related.eq_def]
    refine ⟨hEnc.1,?_⟩
    intro Δ hd he
    obtain ⟨_,hBits,hApp⟩ := hEnc.2 Δ hd he
    constructor
    · intro t ho
      obtain ⟨hW,hS⟩ := hBits t ho
      exact ⟨fun h => ProtectedSpineSoundLambdaBitsProof.bit F M α body ih Γ Δ types vs cs
        hm hw hf ht hu hd he t ho false (hW.symm.trans h),
        fun h => ProtectedSpineSoundLambdaBitsProof.bit F M α body ih Γ Δ types vs cs
          hm hw hf ht hu hd he t ho true (hS.symm.trans h)⟩
    · intro ds τ hp xs args hx htArgs huArgs hrArgs
      have hFrame := ProtectedSpineSoundFrameProof.restrict F Γ Δ types vs cs hw hd he hf
      have hSource := DecisionSourceBasicProof.weakening _ _ _ _ _ _ he hBody
      rw [hApp ds τ hp xs hx]
      cases ds with
      | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp).1 rfl)
      | cons d ds =>
        cases xs with
        | nil => have h := hx.1; simp at h
        | cons x xs =>
          have h := ProtectedSpineSoundLambdaCallProof.call F M α body ih Δ types vs
            (weakenBound E Γ Δ cs) hd hFrame ht hSource .nil vs rfl d ds x xs τ args hp hx htArgs huArgs hrArgs
          have hn := ProtectedSpineSoundTupleProof.nonempty hp htArgs
          cases args with
          | nil => exact False.elim hn
          | cons a args => exact h
  · intro consumed outer hEq ds τ xs args hp hx hArgs hSource hr
    cases ds with
    | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp).1 rfl)
    | cons d ds =>
      cases xs with
      | nil => have h := hx.1; simp at h
      | cons x xs =>
        exact ProtectedSpineSoundLambdaCallProof.call F M α body ih Γ types vs cs hw hf ht hBody
          consumed outer hEq d ds x xs τ args hp hx hArgs hSource hr

end LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaProof
