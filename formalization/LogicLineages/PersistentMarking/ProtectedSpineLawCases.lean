import LogicLineages.PersistentMarking.ProtectedSpineHeadProof
import LogicLineages.PersistentMarking.ProtectedSpineLambdaProof
import LogicLineages.PersistentMarking.ProtectedSpineVariableProof
import LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
import LogicLineages.PersistentMarking.SpineShiftProof

namespace LogicLineages.PersistentMarking.ProtectedSpineLawCases
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineLaws ProtectedSpineInterpreter
open MarkedConstructorTargets (PrefixClosed)
open ProtectedSpineCoverageProof

def ExprLaw (S : Signature) (E : Environment) (H : List Head) (M : Code) (q : Expr) : Prop :=
  ∀ C σ, Typed C q σ → Covered E H q → EvaluationLaws E σ (evaluate S E H M q)

def ArgsLaw (S : Signature) (E : Environment) (H : List Head) (M : Code) (qs : Args) : Prop :=
  ∀ C, ArgsCovered E H qs →
    (∀ types, BaseTyped C qs types → ArgumentLaws E (evaluateArgs S E H M qs) types) ∧
    (ExtrasTyped C qs → ArgumentLaws E (evaluateArgs S E H M qs) ((MarkedConstructorTests.terms qs).map Expr.type))

theorem free (S : Signature) (E : Environment) (H : List Head) (M : Code) (α : Ty) (x : Nat) :
    ExprLaw S E H M (.free α x) := by
  intro C σ h _
  cases h
  exact ProtectedSpineVariableProof.free S E H M _ _

theorem bound (S : Signature) (E : Environment) (H : List Head) (M : Code) (α : Ty) (i : Nat) :
    ExprLaw S E H M (.bound α i) := by
  intro C σ h _
  cases h
  exact ProtectedSpineVariableProof.bound S E H M _ _

theorem lam (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (α : Ty) (q : Expr) (ih : ExprLaw S E H M q) : ExprLaw S E H M (.lam α q) := by
  intro C σ h hq
  cases h with
  | lam hbody =>
    have hbodyLaws := ih (C.push α) _ hbody (lambdaBody E H α q hq)
    have hρ := SpineShiftProof.annotationExact _ _ _ hbody
    have hbodyLaws' : EvaluationLaws E q.type (evaluate S E H M q) := hρ.symm ▸ hbodyLaws
    have hlam := ProtectedSpineLambdaProof.laws E α q.type (evaluate S E H M q)
      (lambdaType E H α q hq) hbodyLaws'
    have he : EvaluationLaws E (.arrow α q.type) (evaluate S E H M (.lam α q)) := hlam
    exact hρ ▸ he

theorem head (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (f : Head) (bs : Args) (ih : ArgsLaw S E H M bs) : ExprLaw S E H M (.head f bs) := by
  intro C σ h hq
  cases h with
  | head hbs =>
    have hbase := (ih C (ordinaryBase E H f bs hq)).1 f.arguments hbs
    have hresult := hq.1 f.result (MarkedConstructorSourceTupleProof.rootSupport (.head f bs))
    exact ProtectedSpineHeadProof.laws false S E H M f f.result (evaluateArgs S E H M bs)
      (fun _ _ _ => []) [] hc hm (hq.2 f List.mem_cons_self) hresult
      (by simp) hbase (ProtectedSpineArgumentProof.nil E)

theorem marked (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (f : Head) (υ : Ty) (bs es : Args) (ih : ArgsLaw S E H M bs) (ih' : ArgsLaw S E H M es) :
    ExprLaw S E H M (.marked f υ bs es) := by
  intro C σ h hq
  cases h with
  | marked hbs hes =>
    have hbase := (ih C (markedBase E H f _ bs es hq)).1 f.arguments hbs
    have hcov := markedExtras E H f _ bs es hq
    have he := (ih' C hcov).2 hes
    have hresult := hq.1 _ (MarkedConstructorSourceTupleProof.rootSupport (.marked f _ bs es))
    exact ProtectedSpineHeadProof.laws true S E H M f _
      (evaluateArgs S E H M bs) (evaluateArgs S E H M es) _ hc hm (hq.2 f List.mem_cons_self) hresult
      (argumentTypes E H es hcov) hbase he

theorem nil (S : Signature) (E : Environment) (H : List Head) (M : Code) : ArgsLaw S E H M .nil := by
  intro C _
  constructor
  · intro types h
    cases h
    exact ProtectedSpineArgumentProof.nil E
  · intro _
    exact ProtectedSpineArgumentProof.nil E

theorem cons (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (q : Expr) (qs : Args) (ih : ExprLaw S E H M q) (ih' : ArgsLaw S E H M qs) :
    ArgsLaw S E H M (.cons q qs) := by
  intro C hq
  obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
  constructor
  · intro types h
    cases h with
    | cons h hqs =>
      have hLaws := ih C _ h hCov
      have hTail := (ih' C hRest).1 _ hqs
      have he := SpineShiftProof.annotationExact _ _ _ h
      have hLaws' : EvaluationLaws E q.type (evaluate S E H M q) := he.symm ▸ hLaws
      have ha : ArgumentLaws E (evaluateArgs S E H M (.cons q qs)) (q.type::_) :=
        ProtectedSpineArgumentProof.cons E q.type _ _ _ hLaws' hTail
      exact he ▸ ha
  · intro h
    cases h with
    | cons h hqs =>
      have hLaws := ih C _ h hCov
      have hTail := (ih' C hRest).2 hqs
      have he := SpineShiftProof.annotationExact _ _ _ h
      have hLaws' : EvaluationLaws E q.type (evaluate S E H M q) := he.symm ▸ hLaws
      exact ProtectedSpineArgumentProof.cons E q.type _ _ _ hLaws' hTail

end LogicLineages.PersistentMarking.ProtectedSpineLawCases
