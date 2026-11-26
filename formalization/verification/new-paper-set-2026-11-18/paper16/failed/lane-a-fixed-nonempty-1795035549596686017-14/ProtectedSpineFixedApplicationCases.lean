import LogicLineages.PersistentMarking.ProtectedSpineConcreteHeadProof
import LogicLineages.PersistentMarking.ProtectedSpineConcreteAuxProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationCases
open Spine NameBridge DecisionInventory DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineFixedApplicationTargets ProtectedSpineConcreteInputProof ProtectedSpineBoundTargets
open ProtectedSpineConcreteAuxProof
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

def AuxLaw (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (args : Args) : Prop :=
  ∀ q vs types τ, BoundImages E H vs types →
    Typed (BoundContext.prefix types EmptyContext) q q.type → Covered E H q →
    CallTyped EmptyContext q.type args τ → ArgsCovered E H args →
    helperAux S E H M Γ q args vs τ = concreteOutput S E H M Γ τ (applyAux q args vs)

theorem emptyCase (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hw : WellFormed E.types E.ports Γ) :
    AuxLaw S E H M Γ .nil := by
  intro q vs types τ hv ht hq ha hArg
  have he : q.type = τ := (argumentTypes q.type .nil τ ha).2.symm
  rw [← he]
  exact ProtectedSpineConcreteAuxProof.empty S E H M Γ q vs types hc hm hw hv ht hq

theorem argumentConsTyped (σ : Ty) (a : Expr) (args : Args) (τ : Ty)
    (h : CallTyped EmptyContext σ (.cons a args) τ) :
    ∃ α ρ, σ = .arrow α ρ ∧ Typed EmptyContext a α ∧ CallTyped EmptyContext ρ args τ := by
  cases h with
  | cons ha hr => exact ⟨_,_,rfl,ha,hr⟩

theorem appendCoverage (E : Environment) (H : List Head) (a : Expr) (vs : Args)
    (ha : Covered E H a) (hv : ArgsCovered E H vs) : ArgsCovered E H (.cons a vs) :=
  ⟨fun σ h => (List.mem_append.mp h).elim (ha.1 σ) (hv.1 σ),
    fun f h => (List.mem_append.mp h).elim (ha.2 f) (hv.2 f)⟩

theorem lambdaCase (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (α : Ty) (body a : Expr) (args vs : Args) (types : List Ty) (τ : Ty)
    (hv : BoundImages E H vs types)
    (ht : Typed (BoundContext.prefix types EmptyContext) (.lam α body) (.lam α body : Expr).type)
    (hq : Covered E H (.lam α body))
    (ha : CallTyped EmptyContext (.arrow α body.type) (.cons a args) τ) (hArg : ArgsCovered E H (.cons a args))
    (ih : AuxLaw S E H M Γ args) :
    helperAux S E H M Γ (.lam α body) (.cons a args) vs τ =
      concreteOutput S E H M Γ τ (applyAux (.lam α body) (.cons a args) vs) := by
  obtain ⟨δ,ρ,hType,hA,hRest⟩ := argumentConsTyped (.arrow α body.type) a args τ ha
  obtain ⟨rfl,hρ⟩ := Ty.arrow.inj hType
  have hTail : CallTyped EmptyContext body.type args τ := hρ.symm ▸ hRest
  have hAnnot := SpineShiftProof.annotationExact EmptyContext a α hA
  have hBody : Typed (BoundContext.prefix (α::types) EmptyContext) body body.type := by
    cases ht with
    | lam h => exact h
  obtain ⟨hACov,hTailCov⟩ := ProtectedSpineCoverageProof.argumentCons E H a args hArg
  have hvs : BoundImages E H (.cons a vs) (α::types) :=
    ⟨.cons hA hv.1,appendCoverage E H a vs hACov hv.2⟩
  rw [lambdaStep S E H M Γ α body a args vs τ hAnnot hTail]
  have he : applyAux (.lam α body) (.cons a args) vs = applyAux body args (.cons a vs) := by
    simp [applyAux,hAnnot]
  rw [he]
  exact ih body _ _ τ hvs hBody (ProtectedSpineCoverageProof.lambdaBody E H α body hq) hTail hTailCov

theorem consCase (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hfix : step S E H M = M) (hw : WellFormed E.types E.ports Γ)
    (a : Expr) (args : Args) (ih : AuxLaw S E H M Γ args) : AuxLaw S E H M Γ (.cons a args) := by
  intro q vs types τ hv ht hq ha hArg
  cases q with
  | free α x => exact freeBlocked S E H M Γ α x a args vs τ hc hm hw ha hArg
  | bound α i =>
    cases ht with
    | bound hi => exact boundBlocked S E H M Γ _ i a args vs types τ hv.1 hi
  | lam α body => exact lambdaCase S E H M Γ α body a args vs types τ hv ht hq ha hArg ih
  | head f bs =>
    cases ht with
    | head hBase =>
      have h := ProtectedSpineConcreteHeadProof.headCall S E H M Γ f f.result τ bs .nil a args vs types
        hc hm hfix hw hv (hq.2 f List.mem_cons_self)
        (hq.1 f.result (MarkedConstructorSourceTupleProof.rootSupport (.head f bs)))
        hBase (ProtectedSpineCoverageProof.ordinaryBase E H f bs hq) .nil
        (by simp [ArgsCovered,auxiliaryArgs,headsArgs]) ha hArg
      have hApp := SpineCallTypingProof.consumeExact EmptyContext f.result (.cons a args) τ ha
      rw [applyAux]
      simpa only [hApp,Option.map_some,substituteArgs,Args.append] using h
  | marked f α bs es =>
    cases ht with
    | marked hBase hExtras =>
      have h := ProtectedSpineConcreteHeadProof.headCall S E H M Γ f _ τ bs es a args vs types
        hc hm hfix hw hv (hq.2 f List.mem_cons_self)
        (hq.1 _ (MarkedConstructorSourceTupleProof.rootSupport (.marked f _ bs es)))
        hBase (ProtectedSpineCoverageProof.markedBase E H f _ bs es hq) hExtras
        (ProtectedSpineCoverageProof.markedExtras E H f _ bs es hq) ha hArg
      have hApp := SpineCallTypingProof.consumeExact EmptyContext _ (.cons a args) τ ha
      rw [applyAux]
      simpa only [hApp,Option.map_some] using h

end LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationCases
