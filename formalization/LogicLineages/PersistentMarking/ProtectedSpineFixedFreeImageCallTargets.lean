import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationTargets
import LogicLineages.PersistentMarking.ProtectedSpineSubstitutionTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineFixedApplicationTargets
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

/-- Interpret the original source with the actual free-image assignments.
The entire nonempty tuple is already concrete in the post-substitution
world. This is a fixed-family equation, including the original none
result; it does not re-encode the arguments under the substitution. -/
def FixedFreeImageNonemptyCall : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q first : Expr) (rest : Args) (τ : Ty) (a : FreeValues),
    let xs : Args := .cons first rest
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    FreeImages E H θ → Typed EmptyContext q q.type → Covered E H q →
    Covered E H (freeSub θ 0 q) →
    CallTyped EmptyContext q.type xs τ → ArgsCovered E H xs →
    InputValid E Γ ⟨a,[]⟩ →
    FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩ →
    call S E H M q Γ a [] (domainTypes xs)
      ((closedCodes S E H M Γ xs).map Prod.snd) τ =
      concreteOutput S E H M Γ τ (apply (freeSub θ 0 q) xs)

end LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallTargets
