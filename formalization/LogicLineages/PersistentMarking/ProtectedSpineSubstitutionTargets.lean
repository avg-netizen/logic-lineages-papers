import LogicLineages.PersistentMarking.ProtectedSpineAgreementTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineSubstitutionTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineAgreementTargets ProtectedSpineInterpreter
open ProtectedSpineEnvironment (freeCode)

def FreeImages (E : Environment) (H : List Head) (θ : FreeMap) : Prop :=
  FreeMapTyped EmptyContext θ ∧ ∀ σ, σ ∈ E.types → ∀ x, Covered E H (θ σ x)

def FreeSubstitutionInputs (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (θ : FreeMap) : FrameRelation :=
  fun Γ a b => a.bound = b.bound ∧
    ∀ σ, σ ∈ E.types → ∀ x, freeCode E Γ a.free σ x =
      codeAt E σ (evaluate S E H M (θ σ x)) Γ ⟨b.free,[]⟩

def FreeSubstitution : Prop := ∀ S E H M θ C q σ depth,
  MarkedConstructorTargets.PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H →
  FreeImages E H θ → Typed C q σ → Covered E H q →
  Agreement E σ (evaluate S E H M q) (evaluate S E H M (freeSub θ depth q))
    (FreeSubstitutionInputs S E H M θ) (· = ·)

end LogicLineages.PersistentMarking.ProtectedSpineSubstitutionTargets
