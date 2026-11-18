import LogicLineages.PersistentMarking.ProtectedSpineFreeCases

namespace LogicLineages.PersistentMarking.ProtectedSpineFreeSubstitutionProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets
open ProtectedSpineFreeCases (ExprSub ArgsSub)
open MarkedConstructorTargets (PrefixClosed)

theorem expression (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hθ : FreeImages E H θ) (q : Expr) : ExprSub S E H M θ q :=
  @Expr.rec (ExprSub S E H M θ) (ArgsSub S E H M θ)
    (ProtectedSpineFreeCases.free S E H M θ hc hm hθ)
    (ProtectedSpineFreeCases.bound S E H M θ)
    (ProtectedSpineFreeCases.lam S E H M θ hc hm hθ)
    (ProtectedSpineFreeCases.head S E H M θ) (ProtectedSpineFreeCases.marked S E H M θ)
    (ProtectedSpineFreeCases.nil S E H M θ) (ProtectedSpineFreeCases.cons S E H M θ hθ) q

theorem exact_FreeSubstitution : FreeSubstitution := by
  intro S E H M θ C q σ depth hc hm hθ hq hcov
  exact expression S E H M θ hc hm hθ q depth C σ hq hcov

#print axioms exact_FreeSubstitution
end LogicLineages.PersistentMarking.ProtectedSpineFreeSubstitutionProof
