import LogicLineages.PersistentMarking.ProtectedSpineBoundCases

namespace LogicLineages.PersistentMarking.ProtectedSpineBoundSubstitutionProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineBoundTargets
open ProtectedSpineBoundCases (ExprSub ArgsSub)
open MarkedConstructorTargets (PrefixClosed)

theorem expression (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hv : BoundImages E H vs removed) (q : Expr) : ExprSub S E H M vs removed q :=
  @Expr.rec (ExprSub S E H M vs removed) (ArgsSub S E H M vs removed)
    (ProtectedSpineBoundCases.free S E H M vs removed)
    (ProtectedSpineBoundCases.bound S E H M vs removed hc hm hv)
    (ProtectedSpineBoundCases.lam S E H M vs removed hc hm hv)
    (ProtectedSpineBoundCases.head S E H M vs removed)
    (ProtectedSpineBoundCases.marked S E H M vs removed)
    (ProtectedSpineBoundCases.nil S E H M vs removed)
    (ProtectedSpineBoundCases.cons S E H M vs removed hv) q

theorem arguments (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hv : BoundImages E H vs removed) (qs : Args) : ArgsSub S E H M vs removed qs :=
  @Args.rec (ExprSub S E H M vs removed) (ArgsSub S E H M vs removed)
    (ProtectedSpineBoundCases.free S E H M vs removed)
    (ProtectedSpineBoundCases.bound S E H M vs removed hc hm hv)
    (ProtectedSpineBoundCases.lam S E H M vs removed hc hm hv)
    (ProtectedSpineBoundCases.head S E H M vs removed)
    (ProtectedSpineBoundCases.marked S E H M vs removed)
    (ProtectedSpineBoundCases.nil S E H M vs removed)
    (ProtectedSpineBoundCases.cons S E H M vs removed hv) qs

theorem exact_BoundSubstitution : BoundSubstitution := by
  intro S E H M vs removed kept q σ hc hm hv hq hcov
  exact expression S E H M vs removed hc hm hv q kept σ hq hcov

#print axioms exact_BoundSubstitution
end LogicLineages.PersistentMarking.ProtectedSpineBoundSubstitutionProof
