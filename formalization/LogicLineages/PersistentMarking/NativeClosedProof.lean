import LogicLineages.PersistentMarking.NativeCarrierTypingProof
import LogicLineages.PersistentMarking.ClosingProof

namespace LogicLineages.PersistentMarking.NativeClosedProof
open Spine NameBridge NativeReduction NativeTypingProof NativeCarrierTargets StructuralContext

theorem lambda (S : Signature) (σ τ : Ty) (q : Expr) (h : ClosedNative S q τ) :
    ClosedNative S (.lam σ q) (.arrow σ τ) :=
  ⟨⟨⟨.lam (ClosingProof.weakening q τ h.1.1.1 (EmptyContext.push σ)),h.1.1.2⟩,
    h.1.2.1,h.1.2.2⟩,h.2⟩

theorem application (S : Signature) (σ τ : Ty) (q a : Expr)
    (hq : ClosedNative S q (.arrow σ τ)) (ha : ClosedNative S a σ) :
    ClosedNative S (app σ τ q a) τ := by
  refine ⟨⟨appPaper S σ τ q a hq.1.1 ha.1.1,appOrdinary σ τ q a hq.1.2.1 ha.1.2.1,?_⟩,?_⟩
  · intro n
    simp [app,freeOccurs,freeOccursArgs,hq.1.2.2 n,ha.1.2.2 n]
  · intro name arity
    simp [app,DecisionInventory.heads,DecisionInventory.headsArgs,hq.2 name arity,ha.2 name arity]

theorem zeroNative (S : Signature) : ClosedNative S zero .ground := by
  exact ⟨⟨zeroPaper S,True.intro,fun _ => rfl⟩,by simp [Native,zero,DecisionInventory.heads,DecisionInventory.headsArgs]⟩

theorem recConstant (S : Signature) (B : Ty) :
    ClosedNative S (.head (.recursor B) .nil) (.arrow .ground (.arrow (stepType B) (.arrow B B))) := by
  exact ⟨⟨recConstantPaper S B,True.intro,fun _ => rfl⟩,by simp [Native,DecisionInventory.heads,DecisionInventory.headsArgs]⟩

theorem recOne (S : Signature) (B : Ty) : ClosedNative S (rec1 B zero) (.arrow (stepType B) (.arrow B B)) :=
  application S .ground (.arrow (stepType B) (.arrow B B)) _ zero (recConstant S B) (zeroNative S)

theorem carrier (S : Signature) (B : Ty) (K U : Expr)
    (hK : ClosedNative S K (.arrow B B)) (hU : ClosedNative S U B) :
    ClosedNative S (W B K U) B := by
  have hF : ClosedNative S (lifted K) (stepType B) := lambda S .ground (.arrow B B) K hK
  have hTwo : ClosedNative S (rec2 B zero (lifted K)) (.arrow B B) :=
    application S (stepType B) (.arrow B B) _ _ (recOne S B) hF
  exact application S B B _ _ hTwo hU

theorem closeAbsent (name : Name) (q : Expr) :
    ∀ d, freeOccurs name q = false → freeSub (closingMap name) d q = q := by
  apply @Expr.rec (fun q => ∀ d, freeOccurs name q = false → freeSub (closingMap name) d q = q)
    (fun qs => ∀ d, freeOccursArgs name qs = false → freeSubArgs (closingMap name) d qs = qs)
  · intro σ x d h
    by_cases he : (σ,x) = name
    · subst name
      simp [freeOccurs] at h
    · simp [freeSub,closingMap,he,shift]
  · intro σ i d h
    rfl
  · intro σ body ih d h
    exact congrArg (Expr.lam σ) (ih (d+1) h)
  · intro f bs ih d h
    exact congrArg (Expr.head f) (ih d h)
  · intro f τ bs es hb he d h
    have h' := Bool.or_eq_false_iff.mp h
    simp only [freeSub,hb d h'.1,he d h'.2]
  · intro d h
    rfl
  · intro a qs ha hq d h
    have h' := Bool.or_eq_false_iff.mp h
    simp only [freeSubArgs,ha d h'.1,hq d h'.2]

theorem closeClosed (name : Name) (q : Expr) (h : Closed q) : close name q = q :=
  closeAbsent name q 0 (h name)

end LogicLineages.PersistentMarking.NativeClosedProof
