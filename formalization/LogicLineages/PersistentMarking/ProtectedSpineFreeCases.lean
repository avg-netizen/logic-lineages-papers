import LogicLineages.PersistentMarking.ProtectedSpineFreeVariableProof
import LogicLineages.PersistentMarking.FreeCallProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFreeCases
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineEnvironment ProtectedSpineLaws
open ProtectedSpineInterpreter ProtectedSpineAgreementTargets ProtectedSpineSubstitutionTargets
open ProtectedSpineCoverageProof ProtectedSpineConstructorAgreementProof
open MarkedConstructorTargets (PrefixClosed)

def ExprSub (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap) (q : Expr) : Prop :=
  ∀ depth C σ, Typed C q σ → Covered E H q →
    Agreement E σ (evaluate S E H M q) (evaluate S E H M (freeSub θ depth q))
      (FreeSubstitutionInputs S E H M θ) (· = ·)

def ArgsSub (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap) (qs : Args) : Prop :=
  ∀ depth C, ExtrasTyped C qs → ArgsCovered E H qs →
    ArgumentsAgree E (FreeSubstitutionInputs S E H M θ)
      (evaluateArgs S E H M qs) (evaluateArgs S E H M (freeSubArgs θ depth qs))

theorem free (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hθ : FreeImages E H θ)
    (α : Ty) (x : Nat) : ExprSub S E H M θ (.free α x) := by
  intro depth C σ h hq
  cases h
  have hσ := hq.1 _ (MarkedConstructorSourceTupleProof.rootSupport (.free _ x))
  exact ProtectedSpineFreeVariableProof.free S E H M θ hc hm hθ _ x depth hσ

theorem bound (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (α : Ty) (i : Nat) : ExprSub S E H M θ (.bound α i) := by
  intro depth C σ h _
  cases h
  exact lookup E _ (fun Γ a => boundCode E Γ a.bound _ i) (fun k => protectedLookup k i) _ _
    (fun Γ a b hr => congrArg (fun bound => boundCode E Γ bound _ i) hr.1)
    (fun _ _ h => congrArg (fun k => protectedLookup k i) h)

theorem lam (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hθ : FreeImages E H θ)
    (α : Ty) (body : Expr) (ih : ExprSub S E H M θ body) : ExprSub S E H M θ (.lam α body) := by
  intro depth C σ h hq
  cases h with
  | lam hbody =>
    let r := freeSub θ (depth+1) body
    let R := FreeSubstitutionInputs S E H M θ
    have hρ := SpineShiftProof.annotationExact _ _ _ hbody
    have hChild := ih (depth+1) (C.push α) _ hbody (lambdaBody E H α body hq)
    have hChild' : Agreement E body.type (evaluate S E H M body) (evaluate S E H M r) R (· = ·) :=
      hρ.symm ▸ hChild
    have hl := ProtectedSpineLambdaAgreementProof.lambda E α body.type _ _ R R (· = ·) (· = ·) hChild'
      (ProtectedSpineFreeInputProof.weaken S E H M θ hc hm hθ)
      (fun Γ a b c _ _ h _ => ProtectedSpineFreeInputProof.push S E H M θ Γ a b α c h)
      (fun _ _ h => congrArg (·+1) h) rfl (lambdaType E H α body hq)
    have hType : r.type = body.type := FreeCallProof.annotation θ
      (fun σ x => SpineShiftProof.annotationExact _ _ _ (hθ.1 σ x)) (depth+1) body
    have he : evaluate S E H M (freeSub θ depth (.lam α body)) =
        ProtectedSpineLambdaCallProof.lambdaEvaluation E α body.type (evaluate S E H M r) := by
      change ProtectedSpineLambdaCallProof.lambdaEvaluation E α r.type (evaluate S E H M r) = _
      rw [hType]
    rw [he]
    exact hρ ▸ hl

theorem head (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (f : Head) (bs : Args) (ih : ArgsSub S E H M θ bs) : ExprSub S E H M θ (.head f bs) := by
  intro depth C σ h hq
  cases h with
  | head hbs =>
    exact ProtectedSpineConstructorAgreementProof.head false S E H M f f.result _ _
      (fun _ _ _ => []) (fun _ _ _ => []) _ _
      (ih depth C (DecisionOccurrenceProof.baseExtras C bs f.arguments hbs) (ordinaryBase E H f bs hq))
      (fun _ _ _ _ _ _ => rfl)

theorem marked (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (f : Head) (υ : Ty) (bs es : Args) (ih : ArgsSub S E H M θ bs) (ih' : ArgsSub S E H M θ es) :
    ExprSub S E H M θ (.marked f υ bs es) := by
  intro depth C σ h hq
  cases h with
  | marked hbs hes =>
    exact ProtectedSpineConstructorAgreementProof.head true S E H M f _ _ _ _ _ _ _
      (ih depth C (DecisionOccurrenceProof.baseExtras C bs f.arguments hbs) (markedBase E H f _ bs es hq))
      (ih' depth C hes (markedExtras E H f _ bs es hq))

theorem nil (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap) :
    ArgsSub S E H M θ .nil := by
  intro depth C h hq Γ a b ha hb hr
  rfl

theorem cons (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (hθ : FreeImages E H θ) (q : Expr) (qs : Args)
    (ih : ExprSub S E H M θ q) (ih' : ArgsSub S E H M θ qs) : ArgsSub S E H M θ (.cons q qs) := by
  intro depth C h hq
  cases h with
  | cons h hqs =>
    obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
    have hv := ih depth C _ h hCov
    have ht := ih' depth C hqs hRest
    have hσ := SpineShiftProof.annotationExact _ _ _ h
    have hv' : Agreement E q.type (evaluate S E H M q) (evaluate S E H M (freeSub θ depth q))
        (FreeSubstitutionInputs S E H M θ) (· = ·) := hσ.symm ▸ hv
    have he : evaluateArgs S E H M (freeSubArgs θ depth (.cons q qs)) =
        ProtectedSpineArgumentProof.consArguments E q.type (evaluate S E H M (freeSub θ depth q))
          (evaluateArgs S E H M (freeSubArgs θ depth qs)) := by
      change ProtectedSpineArgumentProof.consArguments E (freeSub θ depth q).type _ _ = _
      rw [FreeCallProof.annotation θ (fun σ x => SpineShiftProof.annotationExact _ _ _ (hθ.1 σ x)) depth q]
    rw [he]
    exact ProtectedSpineConstructorAgreementProof.cons E q.type _ _ _ _ _ _ hv' ht

end LogicLineages.PersistentMarking.ProtectedSpineFreeCases
