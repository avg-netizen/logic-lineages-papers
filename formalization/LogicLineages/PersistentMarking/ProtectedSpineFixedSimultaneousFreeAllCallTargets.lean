import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeCallTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineFixedApplicationTargets
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

/-- The same simultaneous fixed-point call on an arbitrary typed original
argument tuple, including the nil tuple. Source and substituted coverage
remain explicit hypotheses. -/
def FixedSimultaneousFreeAllCall : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q : Expr) (xs : Args) (τ : Ty) (a : FreeValues),
    let ys := freeSubArgs θ 0 xs
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    FreeImages E H θ → Typed EmptyContext q q.type → Covered E H q →
    Covered E H (freeSub θ 0 q) →
    CallTyped EmptyContext q.type xs τ → ArgsCovered E H xs → ArgsCovered E H ys →
    InputValid E Γ ⟨a,[]⟩ →
    FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩ →
    call S E H M q Γ a [] (domainTypes xs)
      ((evaluateArgs S E H M xs Γ a []).map Prod.snd) τ =
      concreteOutput S E H M Γ τ (apply (freeSub θ 0 q) ys)

end LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallTargets
