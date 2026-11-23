module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLawCases

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineInterpretationProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineLaws ProtectedSpineInterpreter
open MarkedConstructorTargets (PrefixClosed)
open ProtectedSpineLawCases (ExprLaw ArgsLaw)

theorem expression (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (q : Expr) :
    ExprLaw S E H M q :=
  @Expr.rec (ExprLaw S E H M) (ArgsLaw S E H M)
    (ProtectedSpineLawCases.free S E H M) (ProtectedSpineLawCases.bound S E H M)
    (ProtectedSpineLawCases.lam S E H M) (ProtectedSpineLawCases.head S E H M hc hm)
    (ProtectedSpineLawCases.marked S E H M hc hm) (ProtectedSpineLawCases.nil S E H M)
    (ProtectedSpineLawCases.cons S E H M) q

theorem arguments (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (qs : Args) :
    ArgsLaw S E H M qs :=
  @Args.rec (ExprLaw S E H M) (ArgsLaw S E H M)
    (ProtectedSpineLawCases.free S E H M) (ProtectedSpineLawCases.bound S E H M)
    (ProtectedSpineLawCases.lam S E H M) (ProtectedSpineLawCases.head S E H M hc hm)
    (ProtectedSpineLawCases.marked S E H M hc hm) (ProtectedSpineLawCases.nil S E H M)
    (ProtectedSpineLawCases.cons S E H M) qs

theorem laws (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (C : BoundContext) (q : Expr) (σ : Ty) (h : Typed C q σ) (hq : Covered E H q) :
    EvaluationLaws E σ (evaluate S E H M q) :=
  expression S E H M hc hm q C σ h hq

theorem baseLaws (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (C : BoundContext) (qs : Args) (types : List Ty) (h : BaseTyped C qs types) (hq : ArgsCovered E H qs) :
    ArgumentLaws E (evaluateArgs S E H M qs) types :=
  (arguments S E H M hc hm qs C hq).1 types h

theorem extraLaws (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (C : BoundContext) (qs : Args) (h : ExtrasTyped C qs) (hq : ArgsCovered E H qs) :
    ArgumentLaws E (evaluateArgs S E H M qs) ((MarkedConstructorTests.terms qs).map Expr.type) :=
  (arguments S E H M hc hm qs C hq).2 h

theorem exact_InterpretationLaws : InterpretationLaws := by
  intro S E H M C q σ hc hm h hq
  exact laws S E H M hc hm C q σ h hq
#print axioms exact_InterpretationLaws
end LogicLineages.PersistentMarking.ProtectedSpineInterpretationProof
