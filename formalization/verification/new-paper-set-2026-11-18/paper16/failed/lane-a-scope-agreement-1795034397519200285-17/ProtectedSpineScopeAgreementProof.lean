import LogicLineages.PersistentMarking.ProtectedSpineConstructorAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineLambdaAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineFrameAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
import LogicLineages.PersistentMarking.SpineShiftProof

namespace LogicLineages.PersistentMarking.ProtectedSpineScopeAgreementProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineEnvironment
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineAgreementTargets
open ProtectedSpineCoverageProof ProtectedSpineConstructorAgreementProof

mutual
theorem scoped (S : Signature) (E : Environment) (H : List Head) (M : Code) (C : BoundContext)
    (q : Expr) (σ : Ty) (h : Typed C q σ) (hq : Covered E H q) :
    Agreement E σ (evaluate S E H M q) (evaluate S E H M q) (SameInputs E C) (SameProtection C) := by
  cases q with
  | free σ x =>
    cases h
    exact lookup E _ (fun Γ a => freeCode E Γ a.free _ x) (fun _ => false) _ _
      (fun _ _ _ hr => hr.1 _ x) (fun _ _ _ => rfl)
  | bound σ i =>
    cases h with
    | bound hi =>
      apply lookup E _ (fun Γ a => boundCode E Γ a.bound _ i) (fun d => protectedLookup d i) _ _
        (fun _ _ _ hr => hr.2 _ i hi)
      intro k l hp
      have he := hp _ i hi
      by_cases hk : i < k
      · simp [protectedLookup,hk,he.mp hk]
      · have hl : ¬i < l := fun h => hk (he.mpr h)
        simp [protectedLookup,hk,hl]
  | lam α body =>
    cases h with
    | lam hbody =>
      have hρ := SpineShiftProof.annotationExact _ _ _ hbody
      have hc := scoped S E H M (C.push α) body _ hbody (lambdaBody E H α body hq)
      have hc' : Agreement E body.type (evaluate S E H M body) (evaluate S E H M body)
          (SameInputs E (C.push α)) (SameProtection (C.push α)) := hρ.symm ▸ hc
      have hl := ProtectedSpineLambdaAgreementProof.lambda E α body.type _ _
        (SameInputs E C) (SameInputs E (C.push α)) (SameProtection C) (SameProtection (C.push α)) hc'
        (ProtectedSpineFrameAgreementProof.weaken E C)
        (fun Γ a b c _ _ h _ => ProtectedSpineFrameAgreementProof.push E C Γ a b α c h)
        (ProtectedSpineFrameAgreementProof.protectPush C α)
        (fun _ _ _ => Iff.rfl) (lambdaType E H α body hq)
      have hl' : Agreement E (.arrow α body.type) (evaluate S E H M (.lam α body))
          (evaluate S E H M (.lam α body)) (SameInputs E C) (SameProtection C) := hl
      exact hρ ▸ hl'
  | head f bs =>
    cases h with
    | head hbs =>
      exact head false S E H M f f.result _ _ (fun _ _ _ => []) (fun _ _ _ => []) _ _
        (baseAgreement S E H M C bs f.arguments hbs (ordinaryBase E H f bs hq))
        (fun _ _ _ _ _ _ => rfl)
  | marked f υ bs es =>
    cases h with
    | marked hbs hes =>
      exact head true S E H M f σ _ _ _ _ _ _
        (baseAgreement S E H M C bs f.arguments hbs (markedBase E H f σ bs es hq))
        (extraAgreement S E H M C es hes (markedExtras E H f σ bs es hq))
termination_by sizeOf q

theorem baseAgreement (S : Signature) (E : Environment) (H : List Head) (M : Code) (C : BoundContext)
    (qs : Args) (types : List Ty) (h : BaseTyped C qs types) (hq : ArgsCovered E H qs) :
    ArgumentsAgree E (SameInputs E C) (evaluateArgs S E H M qs) (evaluateArgs S E H M qs) := by
  cases qs with
  | nil => intro Γ a b _ _ _; rfl
  | cons q qs =>
    cases h with
    | cons h hqs =>
      obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
      have hv := scoped S E H M C q _ h hCov
      have ht := baseAgreement S E H M C qs _ hqs hRest
      have hσ := SpineShiftProof.annotationExact _ _ _ h
      have hv' : Agreement E q.type (evaluate S E H M q) (evaluate S E H M q)
          (SameInputs E C) (SameProtection C) := hσ.symm ▸ hv
      exact cons E q.type _ _ _ _ _ _ hv' ht
termination_by sizeOf qs

theorem extraAgreement (S : Signature) (E : Environment) (H : List Head) (M : Code) (C : BoundContext)
    (qs : Args) (h : ExtrasTyped C qs) (hq : ArgsCovered E H qs) :
    ArgumentsAgree E (SameInputs E C) (evaluateArgs S E H M qs) (evaluateArgs S E H M qs) := by
  cases qs with
  | nil => intro Γ a b _ _ _; rfl
  | cons q qs =>
    cases h with
    | cons h hqs =>
      obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
      have hv := scoped S E H M C q _ h hCov
      have ht := extraAgreement S E H M C qs hqs hRest
      have hσ := SpineShiftProof.annotationExact _ _ _ h
      have hv' : Agreement E q.type (evaluate S E H M q) (evaluate S E H M q)
          (SameInputs E C) (SameProtection C) := hσ.symm ▸ hv
      exact cons E q.type _ _ _ _ _ _ hv' ht
termination_by sizeOf qs
end

theorem exact_ScopeAgreement : ScopeAgreement := scoped
#print axioms exact_ScopeAgreement
end LogicLineages.PersistentMarking.ProtectedSpineScopeAgreementProof
