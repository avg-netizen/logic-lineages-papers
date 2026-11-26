module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineBoundVariableProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineBoundCases
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineEnvironment
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineAgreementTargets ProtectedSpineBoundTargets
open ProtectedSpineCoverageProof ProtectedSpineConstructorAgreementProof
open MarkedConstructorTargets (PrefixClosed)

abbrev oldScope (removed kept : List Ty) : BoundContext :=
  BoundContext.prefix kept (BoundContext.prefix removed EmptyContext)

def ExprSub (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (q : Expr) : Prop :=
  ∀ kept σ, Typed (oldScope removed kept) q σ → Covered E H q →
    Agreement E σ (evaluate S E H M q) (evaluate S E H M (substitute vs kept.length q))
      (BoundSubstitutionInputs S E H M vs kept) (RetainedProtection kept)

def ArgsSub (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (qs : Args) : Prop :=
  ∀ kept, ExtrasTyped (oldScope removed kept) qs → ArgsCovered E H qs →
    ArgumentsAgree E (BoundSubstitutionInputs S E H M vs kept)
      (evaluateArgs S E H M qs) (evaluateArgs S E H M (substituteArgs vs kept.length qs))

theorem free (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (α : Ty) (x : Nat) : ExprSub S E H M vs removed (.free α x) := by
  intro kept σ h hq
  cases h
  exact lookup E _ (fun Γ a => freeCode E Γ a.free _ x) (fun _ => false) _ _
    (fun _ _ _ hr => hr.1 _ x) (fun _ _ _ => rfl)

theorem bound (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hv : BoundImages E H vs removed) (α : Ty) (i : Nat) : ExprSub S E H M vs removed (.bound α i) := by
  intro kept σ h hq
  cases h with
  | bound hi => exact ProtectedSpineBoundVariableProof.bound S E H M vs removed kept hc hm hv _ i hi

theorem annotation (vs : Args) (removed kept : List Ty) (hv : BaseTyped EmptyContext vs removed)
    (q : Expr) (σ : Ty) (hq : Typed (oldScope removed kept) q σ) :
    (substitute vs kept.length q).type = q.type :=
  (SpineShiftProof.annotationExact _ _ _
    (SpineSubstitutionProof.preserves _ _ q σ vs kept.length hq
      (ProtectedSpineBoundSyntaxProof.compatible vs removed kept hv))).trans
    (SpineShiftProof.annotationExact _ _ _ hq).symm

theorem lam (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hv : BoundImages E H vs removed) (α : Ty) (body : Expr)
    (ih : ExprSub S E H M vs removed body) : ExprSub S E H M vs removed (.lam α body) := by
  intro kept σ h hq
  cases h with
  | lam hbody =>
    let r := substitute vs (kept.length+1) body
    let R := BoundSubstitutionInputs S E H M vs
    have hρ := SpineShiftProof.annotationExact _ _ _ hbody
    have hChild := ih (α::kept) _ hbody (lambdaBody E H α body hq)
    have hChild' : Agreement E body.type (evaluate S E H M body) (evaluate S E H M r)
        (R (α::kept)) (RetainedProtection (α::kept)) := hρ.symm ▸ hChild
    have hl := ProtectedSpineLambdaAgreementProof.lambda E α body.type _ _ (R kept) (R (α::kept))
      (RetainedProtection kept) (RetainedProtection (α::kept)) hChild'
      (ProtectedSpineBoundInputProof.weaken S E H M vs removed kept hc hm hv)
      (fun Γ a b c _ _ h _ => ProtectedSpineBoundInputProof.push S E H M vs kept Γ a b α c h)
      (fun k l h => ⟨congrArg (·+1) h.1,Nat.succ_le_succ h.2⟩)
      ⟨rfl,Nat.zero_le _⟩ (lambdaType E H α body hq)
    have hType : r.type = body.type := annotation vs removed (α::kept) hv.1 body _ hbody
    have he : evaluate S E H M (substitute vs kept.length (.lam α body)) =
        ProtectedSpineLambdaCallProof.lambdaEvaluation E α body.type (evaluate S E H M r) := by
      change ProtectedSpineLambdaCallProof.lambdaEvaluation E α r.type (evaluate S E H M r) = _
      rw [hType]
    rw [he]
    exact hρ ▸ hl

theorem head (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (f : Head) (bs : Args) (ih : ArgsSub S E H M vs removed bs) :
    ExprSub S E H M vs removed (.head f bs) := by
  intro kept σ h hq
  cases h with
  | head hbs =>
    exact ProtectedSpineConstructorAgreementProof.head false S E H M f f.result _ _
      (fun _ _ _ => []) (fun _ _ _ => []) _ _
      (ih kept (DecisionOccurrenceProof.baseExtras _ bs f.arguments hbs) (ordinaryBase E H f bs hq))
      (fun _ _ _ _ _ _ => rfl)

theorem marked (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (f : Head) (υ : Ty) (bs es : Args)
    (ih : ArgsSub S E H M vs removed bs) (ih' : ArgsSub S E H M vs removed es) :
    ExprSub S E H M vs removed (.marked f υ bs es) := by
  intro kept σ h hq
  cases h with
  | marked hbs hes =>
    exact ProtectedSpineConstructorAgreementProof.head true S E H M f _ _ _ _ _ _ _
      (ih kept (DecisionOccurrenceProof.baseExtras _ bs f.arguments hbs) (markedBase E H f _ bs es hq))
      (ih' kept hes (markedExtras E H f _ bs es hq))

theorem nil (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) : ArgsSub S E H M vs removed .nil := by
  intro kept h hq Γ a b ha hb hr
  rfl

theorem cons (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (hv : BoundImages E H vs removed) (q : Expr) (qs : Args)
    (ih : ExprSub S E H M vs removed q) (ih' : ArgsSub S E H M vs removed qs) :
    ArgsSub S E H M vs removed (.cons q qs) := by
  intro kept h hq
  cases h with
  | cons h hqs =>
    obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
    have hσ := SpineShiftProof.annotationExact _ _ _ h
    have ha := ih kept _ h hCov
    have ha' : Agreement E q.type (evaluate S E H M q) (evaluate S E H M (substitute vs kept.length q))
        (BoundSubstitutionInputs S E H M vs kept) (RetainedProtection kept) := hσ.symm ▸ ha
    have hEq : evaluateArgs S E H M (substituteArgs vs kept.length (.cons q qs)) =
        ProtectedSpineArgumentProof.consArguments E q.type
          (evaluate S E H M (substitute vs kept.length q))
          (evaluateArgs S E H M (substituteArgs vs kept.length qs)) := by
      change ProtectedSpineArgumentProof.consArguments E (substitute vs kept.length q).type _ _ = _
      rw [annotation vs removed kept hv.1 q _ h]
    rw [hEq]
    exact ProtectedSpineConstructorAgreementProof.cons E q.type _ _ _ _ _ _ ha' (ih' kept hqs hRest)

end LogicLineages.PersistentMarking.ProtectedSpineBoundCases
