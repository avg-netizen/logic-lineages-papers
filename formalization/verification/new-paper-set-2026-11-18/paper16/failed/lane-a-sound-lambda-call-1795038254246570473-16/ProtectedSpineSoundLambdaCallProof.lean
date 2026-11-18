import LogicLineages.PersistentMarking.ProtectedSpineSoundCallSyntaxProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundTupleProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaCallProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineInterpreterCore ProtectedSpineLaws
open ProtectedSpineSoundInterpreterTargets

theorem callMeasure {σ τ : Ty} {args : Args} (h : CallTyped EmptyContext σ args τ) :
    typeSize τ ≤ typeSize σ ∧ (Spine.Nonempty args → typeSize τ < typeSize σ) := by
  induction h with
  | nil => exact ⟨Nat.le_refl _,fun h => False.elim h⟩
  | cons _ _ ih =>
    have hs := ih.1
    simp only [typeSize]
    exact ⟨by omega,fun _ => by omega⟩

theorem call (F : Inputs S) (M : Code) (α : Ty) (body : Expr)
    (ih : ExprGoal F M body)
    (Γ : Context) (types : List Ty) (vs : Args) (cs : BoundValues)
    (hw : WellFormed F.data.types F.data.ports Γ) (hf : Frame F Γ types vs cs)
    (ht : Typed (BoundContext.prefix (α::types) EmptyContext) body body.type)
    (hu : Source F Γ body) (consumed outer : Args) (hVs : vs = consumed.append outer)
    (d : Ty) (ds : List Ty) (x : Code) (xs : List Code) (τ : Ty) (args : Args)
    (hp : (d::ds,τ) ∈ fullPrefixes (.arrow α body.type))
    (hx : TupleValues (domain F) Γ (d::ds) (x::xs))
    (hArgs : CallTyped EmptyContext (.arrow α body.type) args τ) (hSource : Sources F Γ args)
    (hr : TupleRelated F Γ (d::ds) (x::xs) args) :
    Related F τ Γ
      (lambdaCall (domain F) α body.type (evaluate S (domain F) F.data.sourceHeads M body)
        Γ [] cs consumed.length d x ds xs τ)
      (applyAux (substitute outer consumed.length (.lam α body)) args consumed) := by
  let E := domain F
  let ev := evaluate S E F.data.sourceHeads M body
  obtain ⟨hd,hRest⟩ := ProtectedSpineSoundCallSyntaxProof.arrowPrefix hp
  subst d
  have hTuple := ((HereditaryTupleProof.tupleCons E Γ α ds x xs).mp hx).2
  have hn := ProtectedSpineSoundTupleProof.nonempty hp hArgs
  cases args with
  | nil => exact False.elim hn
  | cons a args =>
    cases hArgs with
    | cons ha hTail =>
      have hType := SpineShiftProof.annotationExact _ _ _ ha
      have haRel : Related F a.type Γ x (some a) := hType.symm ▸ hr 0 α x a rfl rfl .here
      have hFrame : Frame F Γ (α::types) (.cons a vs) ((α,x)::cs) := by
        have hb := BaseRelated.cons haRel hf.2.2
        rw [hType] at hb
        exact ⟨.cons ha hf.1,⟨hSource.1,hf.2.1⟩,hb⟩
      let used := Args.cons a consumed
      have hLen : consumed.length+1 = used.length := by simp [used,Args.length,Nat.add_comm]
      have hMulti : Args.cons a vs = used.append outer := congrArg (Args.cons a) hVs
      have hConcrete : applyAux (substitute outer consumed.length (.lam α body)) (.cons a args) consumed =
          applyAux (substitute outer used.length body) args used := by
        simp only [substitute,applyAux,hType,if_true,hLen]
        rfl
      rw [hConcrete]
      have hBody := ih Γ (α::types) (.cons a vs) ((α,x)::cs) ht hu hw hFrame
      rcases hRest with ⟨hDs,hTy⟩ | hp'
      · subst ds
        subst τ
        have hXs : xs = [] := List.eq_nil_of_length_eq_zero hTuple.1.symm
        subst xs
        cases args with
        | nil =>
          rw [ProtectedSpineSoundCallSyntaxProof.emptyCombined used outer body,←hMulti]
          simpa only [lambdaCall,if_pos rfl,if_true] using hBody.1
        | cons b args =>
          have hMeasure := (callMeasure hTail).2 trivial
          exact False.elim (Nat.lt_irrefl _ hMeasure)
      · cases ds with
        | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp').1 rfl)
        | cons d ds =>
          cases xs with
          | nil => have hn := hTuple.1; simp at hn
          | cons c xs =>
            have hNewTuple : TupleRelated F Γ (d::ds) (c::xs) args :=
              fun i ρ v q hd hv hq => hr (i+1) ρ v q hd hv (.there hq)
            have h := hBody.2 used outer hMulti (d::ds) τ (c::xs) args hp' hTuple hTail hSource.2 hNewTuple
            simp only [lambdaCall,if_pos rfl,if_true]
            change Related F τ Γ (ev.nonempty Γ [] ((α,x)::cs) (consumed.length+1) d c ds xs τ) _
            rw [hLen]
            exact h

end LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaCallProof
