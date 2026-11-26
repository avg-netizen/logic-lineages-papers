module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineScopeCases

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineScopeAgreementProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineAgreementTargets
open ProtectedSpineScopeCases (ExprScope ArgsScope)

theorem expression (S : Signature) (E : Environment) (H : List Head) (M : Code) (q : Expr) :
    ExprScope S E H M q :=
  @Expr.rec (ExprScope S E H M) (ArgsScope S E H M)
    (ProtectedSpineScopeCases.free S E H M) (ProtectedSpineScopeCases.bound S E H M)
    (ProtectedSpineScopeCases.lam S E H M) (ProtectedSpineScopeCases.head S E H M)
    (ProtectedSpineScopeCases.marked S E H M) (ProtectedSpineScopeCases.nil S E H M)
    (ProtectedSpineScopeCases.cons S E H M) q

theorem exact_ScopeAgreement : ScopeAgreement := by
  intro S E H M C q σ h hq
  exact expression S E H M q C σ h hq
#print axioms exact_ScopeAgreement
end LogicLineages.PersistentMarking.ProtectedSpineScopeAgreementProof
