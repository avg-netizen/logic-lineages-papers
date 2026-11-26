import LogicLineages.PersistentMarking.StructuralInterpretationCorrectedTargets
import LogicLineages.PersistentMarking.ProtectedSpineFiniteConcreteEnvironmentProof

namespace LogicLineages.PersistentMarking.Paper16StructuralScopeTargets
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode
open Grafting TypeSupport
open ProtectedSpineFixedMixedFrameCallTargets (helperWithFree)
open ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineAgreementTargets (Agreement)
open ProtectedSpineEnvironment (FreeValues)
open ProtectedSpineSubstitutionTargets ProtectedSpineBoundTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineStructuralConcreteProof
open ProtectedSpineFiniteConcreteEnvironmentProof
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

/-- Value agreement under a finitely supported, type-preserving
substitution by ordinary terms. The relation evaluates images in the
destination free frame. Every retained interpretation stage is in scope. -/
def NamedValueSubstitution : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (η : NamedMap) (q : Term) (σ : Ty) (names : List Name),
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H →
    SupportedNamedMap names η → NamedOrdinaryMap S η → FreeImages E H (encodeMap η) →
    NamedTyped q σ → Covered E H (encode [] q) →
    Agreement E σ (evaluate S E H M (encode [] q))
      (evaluate S E H M (encode [] (namedSubstitute η q)))
      (FreeSubstitutionInputs S E H M (encodeMap η)) (· = ·)

/-- Full application at any valid frame that interprets the concrete
substitution in the literal destination frame. -/
def RelatedFrameFixedApplication : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (η : NamedMap) (q : Term) (xs : List Term) (σ τ : Ty) (a : FreeValues),
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    NamedMapTyped η → FreeImages E H (encodeMap η) → NamedTyped q σ →
    Covered E H (encode [] q) → NamedExtras xs →
    CallTyped EmptyContext (encode [] q).type (encodeArgs [] xs) τ →
    ArgsCovered E H (encodeArgs [] xs) → InputValid E Γ ⟨a,[]⟩ →
    FreeSubstitutionInputs S E H M (encodeMap η) Γ ⟨a,[]⟩ ⟨[],[]⟩ →
    call S E H M (encode [] q) Γ a [] (domainTypes (encodeArgs [] xs))
      ((evaluateArgs S E H M (encodeArgs [] xs) Γ a []).map Prod.snd) τ =
      concreteOutput S E H M Γ τ
        (apply (encode [] (namedSubstitute η q)) (encodeArgs [] (xs.map (namedSubstitute η))))

/-- Full application of the substituted named source, with its concrete
finite environment constructed from the substitution images. -/
def NamedFixedApplication : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (η : NamedMap) (q : Term) (xs : List Term) (σ τ : Ty) (names : List Name),
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    WellFormed E.types E.ports Γ → (∀ n ∈ names, n.1 ∈ E.types) →
    SupportedNamedMap names η → NamedMapTyped η → FreeImages E H (encodeMap η) →
    NamedTyped q σ → Covered E H (encode [] q) → NamedExtras xs →
    CallTyped EmptyContext (encode [] q).type (encodeArgs [] xs) τ →
    ArgsCovered E H (encodeArgs [] xs) →
    let a := canonicalValues S E H M (encodeMap η) Γ names
    call S E H M (encode [] q) Γ a [] (domainTypes (encodeArgs [] xs))
      ((evaluateArgs S E H M (encodeArgs [] xs) Γ a []).map Prod.snd) τ =
      concreteOutput S E H M Γ τ
        (apply (encode [] (namedSubstitute η q)) (encodeArgs [] (xs.map (namedSubstitute η))))

/-- The helper after consuming a literal binder prefix. The call arguments
remain outside that prefix, and evaluation of an undefined substituted
application uses the actual bottom code. -/
def ConsumedPrefixFixedApplication : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q : Expr) (xs consumed : Args) (types : List Ty) (τ : Ty) (names : List Name),
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    WellFormed E.types E.ports Γ → (∀ n ∈ names, n.1 ∈ E.types) →
    SupportedFreeMap names θ → FreeImages E H θ → BoundImages E H consumed types →
    Typed (BoundContext.prefix types EmptyContext) q q.type → Covered E H q →
    CallTyped EmptyContext q.type xs τ → ArgsCovered E H xs →
    helperWithFree S E H M Γ q xs consumed (canonicalValues S E H M θ Γ names) τ =
      concreteOutput S E H M Γ τ (applyAux (freeSub θ 0 q) (freeSubArgs θ 0 xs) consumed)

/-- The complete conjunction to compare against the current
structural-interpretation paragraph. The fixed point applies to the
substituted-source call equations through their own hypotheses. -/
def StructuralInterpretation : Prop :=
  InterpretationLaws ∧ FreeSubstitution ∧ BoundSubstitution ∧ NamedValueSubstitution ∧
    RelatedFrameFixedApplication ∧ NamedFixedApplication ∧ ConsumedPrefixFixedApplication

def StructuralInterpretationWithBoundary : Prop :=
  StructuralInterpretation ∧ ProtectedSpineApplicationCounterexampleTargets.AvailabilityGap

end LogicLineages.PersistentMarking.Paper16StructuralScopeTargets
