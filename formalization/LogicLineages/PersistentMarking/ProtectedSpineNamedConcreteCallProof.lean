import LogicLineages.PersistentMarking.ProtectedSpineStructuralConcreteProof
import LogicLineages.PersistentMarking.GraftingProof

namespace LogicLineages.PersistentMarking.ProtectedSpineNamedConcreteCallProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode Grafting TypeSupport
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineStructuralConcreteProof (exact_FixedConcreteWholeCall)
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

theorem exact_NamedConcreteTupleEncoding (η : NamedMap) (images : NamedMapTyped η)
    (xs : List Term) (typed : NamedExtras xs) :
    encodeArgs [] (xs.map (namedSubstitute η)) = freeSubArgs (encodeMap η) 0 (encodeArgs [] xs) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    cases typed with
    | cons h t =>
      simp only [List.map_cons,encodeArgs,freeSubArgs,ih t,
        GraftingProof.typedNamedSubstitutionEncoding _ _ _ images h]

/-- The outer-syntax interpretation uses actual capture-avoiding named
substitution on both the source and the ordered tuple before the fixed
point's full application. The Lean constructor scope is not inferred
from a mere equality of numerical codes. -/
theorem exact_NamedFixedConcreteWholeCall
    (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (η : NamedMap) (q : Term) (xs : List Term) (σ τ : Ty) (a : FreeValues)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (fix : step S E H M = M)
    (imageTyping : NamedMapTyped η) (images : FreeImages E H (encodeMap η)) (typed : NamedTyped q σ)
    (covered : Covered E H (encode [] q)) (extra : NamedExtras xs)
    (callTy : CallTyped EmptyContext (encode [] q).type (encodeArgs [] xs) τ)
    (argsCovered : ArgsCovered E H (encodeArgs [] xs))
    (valid : InputValid E Γ ⟨a,[]⟩)
    (related : FreeSubstitutionInputs S E H M (encodeMap η) Γ ⟨a,[]⟩ ⟨[],[]⟩) :
    call S E H M (encode [] q) Γ a [] (domainTypes (encodeArgs [] xs))
      ((evaluateArgs S E H M (encodeArgs [] xs) Γ a []).map Prod.snd) τ =
      concreteOutput S E H M Γ τ
        (apply (encode [] (namedSubstitute η q)) (encodeArgs [] (xs.map (namedSubstitute η)))) := by
  have qTyped := BridgeTypingProof.encodeTyped [] q σ typed
  have qType : (encode [] q).type = σ := SpineShiftProof.annotationExact _ _ _ qTyped
  have input : Typed EmptyContext (encode [] q) (encode [] q).type := by
    rw [qType]
    exact qTyped
  rw [GraftingProof.typedNamedSubstitutionEncoding η q σ imageTyping typed,
    exact_NamedConcreteTupleEncoding η imageTyping xs extra]
  exact exact_FixedConcreteWholeCall S E H M Γ (encodeMap η) (encode [] q) (encodeArgs [] xs) τ a
    hc hm fix images input covered callTy argsCovered valid related

#print axioms exact_NamedConcreteTupleEncoding
#print axioms exact_NamedFixedConcreteWholeCall
end LogicLineages.PersistentMarking.ProtectedSpineNamedConcreteCallProof
