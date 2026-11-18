import LogicLineages.PersistentMarking.ProtectedSpineConstructorAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineLambdaAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineFrameAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
import LogicLineages.PersistentMarking.SpineShiftProof

namespace LogicLineages.PersistentMarking.ProtectedSpineScopeCases
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineEnvironment
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineAgreementTargets
open ProtectedSpineCoverageProof ProtectedSpineConstructorAgreementProof

def ExprScope (S : Signature) (E : Environment) (H : List Head) (M : Code) (q : Expr) : Prop :=
  ∀ C σ, Typed C q σ → Covered E H q →
    Agreement E σ (evaluate S E H M q) (evaluate S E H M q) (SameInputs E C) (SameProtection C)

def ArgsScope (S : Signature) (E : Environment) (H : List Head) (M : Code) (qs : Args) : Prop :=
  ∀ C, ExtrasTyped C qs → ArgsCovered E H qs →
    ArgumentsAgree E (SameInputs E C) (evaluateArgs S E H M qs) (evaluateArgs S E H M qs)

theorem free (S : Signature) (E : Environment) (H : List Head) (M : Code) (α : Ty) (x : Nat) :
    ExprScope S E H M (.free α x) := by
  intro C σ h _
  cases h
  exact lookup E _ (fun Γ a => freeCode E Γ a.free _ x) (fun _ => false) _ _
    (fun _ _ _ hr => hr.1 _ x) (fun _ _ _ => rfl)

theorem bound (S : Signature) (E : Environment) (H : List Head) (M : Code) (α : Ty) (i : Nat) :
    ExprScope S E H M (.bound α i) := by
  intro C σ h _
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

theorem lam (S : Signature) (E : Environment) (H : List Head) (M : Code) (α : Ty) (body : Expr)
    (ih : ExprScope S E H M body) : ExprScope S E H M (.lam α body) := by
  intro C σ h hq
  cases h with
  | lam hbody =>
    have hρ := SpineShiftProof.annotationExact _ _ _ hbody
    have hc := ih (C.push α) _ hbody (lambdaBody E H α body hq)
    have hc' : Agreement E body.type (evaluate S E H M body) (evaluate S E H M body)
        (SameInputs E (C.push α)) (SameProtection (C.push α)) := hρ.symm ▸ hc
    have hl := ProtectedSpineLambdaAgreementProof.lambda E α body.type _ _
      (SameInputs E C) (SameInputs E (C.push α)) (SameProtection C) (SameProtection (C.push α)) hc'
      (ProtectedSpineFrameAgreementProof.weaken E C)
      (fun Γ a b c _ _ hr _ => ProtectedSpineFrameAgreementProof.push E C Γ a b α c hr)
      (ProtectedSpineFrameAgreementProof.protectPush C α)
      (fun _ _ _ => Iff.rfl) (lambdaType E H α body hq)
    have hl' : Agreement E (.arrow α body.type) (evaluate S E H M (.lam α body))
        (evaluate S E H M (.lam α body)) (SameInputs E C) (SameProtection C) := hl
    exact hρ ▸ hl'

theorem head (S : Signature) (E : Environment) (H : List Head) (M : Code) (f : Head) (bs : Args)
    (ih : ArgsScope S E H M bs) : ExprScope S E H M (.head f bs) := by
  intro C σ h hq
  cases h with
  | head hbs =>
    exact ProtectedSpineConstructorAgreementProof.head false S E H M f f.result _ _
      (fun _ _ _ => []) (fun _ _ _ => []) _ _
      (ih C (DecisionOccurrenceProof.baseExtras C bs f.arguments hbs) (ordinaryBase E H f bs hq))
      (fun _ _ _ _ _ _ => rfl)

theorem marked (S : Signature) (E : Environment) (H : List Head) (M : Code) (f : Head)
    (υ : Ty) (bs es : Args) (ih : ArgsScope S E H M bs) (ih' : ArgsScope S E H M es) :
    ExprScope S E H M (.marked f υ bs es) := by
  intro C σ h hq
  cases h with
  | marked hbs hes =>
    exact ProtectedSpineConstructorAgreementProof.head true S E H M f _ _ _ _ _ _ _
      (ih C (DecisionOccurrenceProof.baseExtras C bs f.arguments hbs) (markedBase E H f _ bs es hq))
      (ih' C hes (markedExtras E H f _ bs es hq))

theorem nil (S : Signature) (E : Environment) (H : List Head) (M : Code) : ArgsScope S E H M .nil := by
  intro C h hq Γ a b ha hb hr
  rfl

theorem cons (S : Signature) (E : Environment) (H : List Head) (M : Code) (q : Expr) (qs : Args)
    (ih : ExprScope S E H M q) (ih' : ArgsScope S E H M qs) : ArgsScope S E H M (.cons q qs) := by
  intro C h hq
  cases h with
  | cons h hqs =>
    obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
    have hv := ih C _ h hCov
    have ht := ih' C hqs hRest
    have hσ := SpineShiftProof.annotationExact _ _ _ h
    have hv' : Agreement E q.type (evaluate S E H M q) (evaluate S E H M q)
        (SameInputs E C) (SameProtection C) := hσ.symm ▸ hv
    exact ProtectedSpineConstructorAgreementProof.cons E q.type _ _ _ _ _ _ hv' ht

end LogicLineages.PersistentMarking.ProtectedSpineScopeCases
