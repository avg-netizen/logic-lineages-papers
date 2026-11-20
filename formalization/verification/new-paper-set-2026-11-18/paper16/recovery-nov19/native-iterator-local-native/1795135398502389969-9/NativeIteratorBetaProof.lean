import LogicLineages.PersistentMarking.NativeIteratorSyntaxProof
import LogicLineages.PersistentMarking.NativeBetaProof
import LogicLineages.PersistentMarking.BoundBlockProof

namespace LogicLineages.PersistentMarking.NativeIteratorBetaProof
open Spine StructuralContext NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorTargets

private theorem lamBody {C σ τ q} (h : Typed C (.lam σ q) (.arrow σ τ)) : Typed (C.push σ) q τ := by
  cases h with
  | lam hq => exact hq

private theorem betaEndpoints {S σ τ body a} (hBody : Typed (EmptyContext.push σ) body τ)
    (hValid : Valid S body) (hOrdinary : Ordinary body) (ha : PaperTerm S a σ) (hoa : Ordinary a) :
    PaperTerm S (app σ τ (.lam σ body) a) τ ∧
      PaperTerm S (substitute (.cons a .nil) 0 body) τ ∧ Ordinary (substitute (.cons a .nil) 0 body) := by
  obtain ⟨⟨ρ, hBefore, hAfter, _, hOrd⟩, _, _⟩ :=
    NativeBetaProof.beta S σ τ body a hBody hValid hOrdinary ha hoa
  have hType : τ = ρ := SpineShiftProof.annotationExact _ _ _ hBefore.1
  subst ρ
  exact ⟨hBefore, hAfter, hOrd⟩

private def callContext (σ τ : Ty) (a : Expr) (inside : Context) : Context :=
  .head (.app σ τ) .nil inside (.cons a .nil)

private theorem typedCallContext {S inside ρ σ τ a}
    (hc : ContextTyped S inside ρ (.arrow σ τ)) (ha : PaperTerm S a σ) (ho : Ordinary a) :
    ContextTyped S (callContext σ τ a inside) ρ τ :=
  .head hc ⟨0, rfl⟩ .nil True.intro True.intro (.cons ha.1 .nil) ⟨ha.2, True.intro⟩ ⟨ho, True.intro⟩ rfl

theorem transport : IteratorNativeBetaTransport := by
  intro S A i p u hi hp hu
  let B := actualType A
  let η := functionType A
  let b₀ := iteratorBody A
  let b₁ := afterIndexBody A i
  let b₂ := afterFunctionBody A i p
  have hIterator := NativeIteratorSyntaxProof.closed S A
  have hBodyI : Typed (EmptyContext.push indexType) (.lam η (.lam B b₀)) (.arrow η η) :=
    .lam (.lam (NativeIteratorSyntaxProof.bodyTyped A))
  obtain ⟨hSourceI, hResultI, hOrdI⟩ := betaEndpoints hBodyI hIterator.1.1.2 hIterator.1.2.1 hi.1.1 hi.1.2.1
  have hStageI : PaperTerm S (.lam η (.lam B b₁)) (.arrow η η) := hResultI
  have hStepI : Reduction S (app indexType (.arrow η η) (iterator A) i) (.lam η (.lam B b₁)) :=
    .primitive (.beta hBodyI hIterator.1.1.2 hIterator.1.2.1 hi.1.1 hi.1.2.1)
  have hCtxI := typedCallContext (typedCallContext (ContextTyped.hole (S := S)) hp.1.1 hp.1.2.1) hu.1.1 hu.1.2.1
  have hEdgeI : Reduction S (applied A i p u) (afterIndex A i p u) :=
    .context hCtxI hSourceI hStageI hStepI

  have hBodyP : Typed (EmptyContext.push η) (.lam B b₁) η := lamBody hStageI.1
  obtain ⟨hSourceP, hResultP, hOrdP⟩ := betaEndpoints hBodyP hStageI.2 hOrdI hp.1.1 hp.1.2.1
  have hStageP : PaperTerm S (.lam B b₂) η := hResultP
  have hStepP : Reduction S (app η η (.lam η (.lam B b₁)) p) (.lam B b₂) :=
    .primitive (.beta hBodyP hStageI.2 hOrdI hp.1.1 hp.1.2.1)
  have hCtxP := typedCallContext (ContextTyped.hole (S := S)) hu.1.1 hu.1.2.1
  have hEdgeP : Reduction S (afterIndex A i p u) (afterFunction A i p u) :=
    .context hCtxP hSourceP hStageP hStepP

  have hStepU : Reduction S (afterFunction A i p u) (substitute (.cons u .nil) 0 b₂) :=
    .primitive (.beta (lamBody hStageP.1) hStageP.2 hOrdP hu.1.1 hu.1.2.1)
  have hFoldP : substitute (.cons u .nil) 0 b₂ = substitute (.cons u (.cons p .nil)) 0 b₁ :=
    BoundBlockProof.block (.cons u .nil) (.cons p .nil) 0 b₁
  have hFoldI : substitute (.cons u (.cons p .nil)) 0 b₁ =
      substitute (.cons u (.cons p (.cons i .nil))) 0 b₀ :=
    BoundBlockProof.block (.cons u (.cons p .nil)) (.cons i .nil) 0 b₀
  have hFinal := hFoldP.trans (hFoldI.trans (NativeIteratorSyntaxProof.literal S A i p u hi hp hu))
  exact ⟨hEdgeI, hEdgeP, hFinal ▸ hStepU⟩

end LogicLineages.PersistentMarking.NativeIteratorBetaProof
