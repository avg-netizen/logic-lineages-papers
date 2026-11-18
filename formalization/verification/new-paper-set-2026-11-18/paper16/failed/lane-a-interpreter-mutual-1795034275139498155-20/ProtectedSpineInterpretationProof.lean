import LogicLineages.PersistentMarking.ProtectedSpineHeadProof
import LogicLineages.PersistentMarking.ProtectedSpineLambdaProof
import LogicLineages.PersistentMarking.ProtectedSpineVariableProof
import LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
import LogicLineages.PersistentMarking.SpineShiftProof

namespace LogicLineages.PersistentMarking.ProtectedSpineInterpretationProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineLaws ProtectedSpineInterpreter
open MarkedConstructorTargets (PrefixClosed)
open ProtectedSpineCoverageProof

mutual
theorem laws (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (C : BoundContext) (q : Expr) (σ : Ty) (h : Typed C q σ) (hq : Covered E H q) :
    EvaluationLaws E σ (evaluate S E H M q) := by
  cases q with
  | free α x => cases h; exact ProtectedSpineVariableProof.free S E H M _ _
  | bound α i => cases h; exact ProtectedSpineVariableProof.bound S E H M _ _
  | lam α body =>
    cases h with
    | lam hbody =>
      have hbodyLaws := laws S E H M hc hm (C.push α) body _ hbody (lambdaBody E H α body hq)
      have hρ := SpineShiftProof.annotationExact _ _ _ hbody
      have hbodyLaws' : EvaluationLaws E body.type (evaluate S E H M body) := hρ.symm ▸ hbodyLaws
      have hlam := ProtectedSpineLambdaProof.laws E α body.type (evaluate S E H M body)
        (lambdaType E H α body hq) hbodyLaws'
      have he : EvaluationLaws E (.arrow α body.type) (evaluate S E H M (.lam α body)) := hlam
      exact hρ ▸ he
  | head f bs =>
    cases h with
    | head hbs =>
      have hbase := baseLaws S E H M hc hm C bs f.arguments hbs (ordinaryBase E H f bs hq)
      have hresult := hq.1 f.result (MarkedConstructorSourceTupleProof.rootSupport (.head f bs))
      exact ProtectedSpineHeadProof.laws false S E H M f f.result (evaluateArgs S E H M bs)
        (fun _ _ _ => []) [] hc hm (hq.2 f List.mem_cons_self) hresult
        (by simp) hbase (ProtectedSpineArgumentProof.nil E)
  | marked f υ bs es =>
    cases h with
    | marked hbs hes =>
      have hbase := baseLaws S E H M hc hm C bs f.arguments hbs (markedBase E H f σ bs es hq)
      have hcov := markedExtras E H f σ bs es hq
      have he := extraLaws S E H M hc hm C es hes hcov
      have hresult := hq.1 σ (MarkedConstructorSourceTupleProof.rootSupport (.marked f σ bs es))
      exact ProtectedSpineHeadProof.laws true S E H M f σ
        (evaluateArgs S E H M bs) (evaluateArgs S E H M es) _ hc hm (hq.2 f List.mem_cons_self) hresult
        (argumentTypes E H es hcov) hbase he
termination_by sizeOf q

theorem baseLaws (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (C : BoundContext) (qs : Args) (types : List Ty) (h : BaseTyped C qs types) (hq : ArgsCovered E H qs) :
    ArgumentLaws E (evaluateArgs S E H M qs) types := by
  cases qs with
  | nil => cases h; exact ProtectedSpineArgumentProof.nil E
  | cons q qs =>
    cases h with
    | cons h hqs =>
      obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
      have hLaws := laws S E H M hc hm C q _ h hCov
      have hTail := baseLaws S E H M hc hm C qs _ hqs hRest
      have he := SpineShiftProof.annotationExact _ _ _ h
      have hLaws' : EvaluationLaws E q.type (evaluate S E H M q) := he.symm ▸ hLaws
      have ha : ArgumentLaws E (evaluateArgs S E H M (.cons q qs)) (q.type::_ ) :=
        ProtectedSpineArgumentProof.cons E q.type _ _ _ hLaws' hTail
      exact he ▸ ha
termination_by sizeOf qs

theorem extraLaws (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (C : BoundContext) (qs : Args) (h : ExtrasTyped C qs) (hq : ArgsCovered E H qs) :
    ArgumentLaws E (evaluateArgs S E H M qs) ((MarkedConstructorTests.terms qs).map Expr.type) := by
  cases qs with
  | nil => cases h; exact ProtectedSpineArgumentProof.nil E
  | cons q qs =>
    cases h with
    | cons h hqs =>
      obtain ⟨hCov,hRest⟩ := argumentCons E H q qs hq
      have hLaws := laws S E H M hc hm C q _ h hCov
      have hTail := extraLaws S E H M hc hm C qs hqs hRest
      have he := SpineShiftProof.annotationExact _ _ _ h
      have hLaws' : EvaluationLaws E q.type (evaluate S E H M q) := he.symm ▸ hLaws
      exact ProtectedSpineArgumentProof.cons E q.type _ _ _ hLaws' hTail
termination_by sizeOf qs
end

theorem exact_InterpretationLaws : InterpretationLaws := by
  intro S E H M C q σ hc hm h hq
  exact laws S E H M hc hm C q σ h hq
#print axioms exact_InterpretationLaws
end LogicLineages.PersistentMarking.ProtectedSpineInterpretationProof
