import LogicLineages.PersistentMarking.StructuralInterpretationCorrectedTargets
import LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineStructuralConcreteTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineBoundTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineFixedMixedFrameCallTargets
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

/-- Paper 16 fixed-point whole call with the original source/tuple and
free images in the finite domain. The substituted source/tuple are not
required to carry separate coverage premises. -/
def FixedConcreteWholeCall : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q : Expr) (xs : Args) (τ : Ty) (a : FreeValues),
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    FreeImages E H θ → Typed EmptyContext q q.type → Covered E H q →
    CallTyped EmptyContext q.type xs τ → ArgsCovered E H xs →
    InputValid E Γ ⟨a,[]⟩ →
    FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩ →
    call S E H M q Γ a [] (domainTypes xs)
      ((evaluateArgs S E H M xs Γ a []).map Prod.snd) τ =
      concreteOutput S E H M Γ τ (apply (freeSub θ 0 q) (freeSubArgs θ 0 xs))

/-- Same closed-image interpretation, inside the actual original helper
with an arbitrary finite prefix of consumed, typed concrete binder
images. Arguments remain outside the consumed binders. -/
def FixedConcretePrefixCall : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q : Expr) (xs consumed : Args) (types : List Ty) (τ : Ty) (a : FreeValues),
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    FreeImages E H θ → BoundImages E H consumed types →
    Typed (BoundContext.prefix types EmptyContext) q q.type → Covered E H q →
    CallTyped EmptyContext q.type xs τ → ArgsCovered E H xs →
    InputValid E Γ ⟨a,[]⟩ →
    FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩ →
    helperWithFree S E H M Γ q xs consumed a τ =
      concreteOutput S E H M Γ τ (applyAux (freeSub θ 0 q) (freeSubArgs θ 0 xs) consumed)

def StructuralConcreteCore : Prop :=
  StructuralInterpretationCorrected.CorrectedStructuralInterpretation ∧
  FixedConcreteWholeCall ∧ FixedConcretePrefixCall

end LogicLineages.PersistentMarking.ProtectedSpineStructuralConcreteTargets
