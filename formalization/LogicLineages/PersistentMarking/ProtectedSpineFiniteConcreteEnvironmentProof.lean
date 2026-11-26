import LogicLineages.PersistentMarking.ProtectedSpineNamedConcreteCallProof
import LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
import LogicLineages.PersistentMarking.ProtectedSpineEncodingProof
import LogicLineages.PersistentMarking.HereditaryCodeReconstructionChecks

namespace LogicLineages.PersistentMarking.ProtectedSpineFiniteConcreteEnvironmentProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode
open Grafting TypeSupport
open ProtectedSpineFixedMixedFrameCallTargets (helperWithFree)
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineBoundTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineStructuralConcreteProof
open ProtectedSpineEnvironmentTargets (FreeValid BoundValid)
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

def SupportedFreeMap (names : List Name) (θ : FreeMap) : Prop :=
  ∀ σ x, (σ,x) ∉ names → θ σ x = .free σ x

def SupportedNamedMap (names : List Name) (η : NamedMap) : Prop :=
  ∀ σ x, (σ,x) ∉ names → η σ x = .var σ x

def canonicalValues (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (θ : FreeMap) (Γ : Context) (names : List Name) : FreeValues :=
  names.map fun n => (n,codeAt E n.1 (evaluate S E H M (θ n.1 n.2)) Γ ⟨[],[]⟩)

private theorem lookupMapped (names : List Name) (f : Name → Code) (n : Name) :
    lookupFree (names.map fun m => (m,f m)) n = if n ∈ names then some (f n) else none := by
  induction names with
  | nil => simp [lookupFree]
  | cons h t ih =>
    by_cases eq : h = n
    · subst h
      simp [lookupFree]
    · have ne : n ≠ h := Ne.symm eq
      simp [lookupFree,eq,ne,ih]

private theorem literalImage (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (σ : Ty) (x : Nat) (hw : WellFormed E.types E.ports Γ) :
    codeAt E σ (evaluate S E H M (.free σ x)) Γ ⟨[],[]⟩ = literalCode E Γ σ x := by
  change HereditaryDomainSemantics.encode E σ Γ
    (HereditaryDomainSemantics.decode E σ Γ (literalCode E Γ σ x)) = _
  exact HereditaryCodeReconstructionChecks.exact_CodeReconstruction E σ Γ _
    (MarkedConstructorLiteralProof.literalRetained E Γ σ x hw)

/-- The literal evaluation of every supported substitution image supplies
a valid finite code environment. Unsupported names get the actual literal
fallback, not an arbitrary default assignment. -/
theorem exact_CanonicalConcreteEnvironment (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (θ : FreeMap) (Γ : Context) (names : List Name)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hw : WellFormed E.types E.ports Γ) (images : FreeImages E H θ)
    (types : ∀ n ∈ names, n.1 ∈ E.types) (support : SupportedFreeMap names θ) :
    let a := canonicalValues S E H M θ Γ names
    InputValid E Γ ⟨a,[]⟩ ∧ FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩ := by
  dsimp only
  refine ⟨⟨hw,?_,by simp [BoundValid]⟩,⟨rfl,?_⟩⟩
  · intro p hp
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
    have laws := ProtectedSpineInterpretationProof.laws S E H M hc hm EmptyContext
      (θ n.1 n.2) n.1 (images.1 n.1 n.2) (images.2 n.1 (types n hn) n.2)
    exact (ProtectedSpineEncodingProof.encodeAt E n.1 _ laws Γ ⟨[],[]⟩
      (ProtectedSpineConcreteInputProof.emptyValid E Γ hw)).1
  · intro σ _ x
    unfold canonicalValues freeCode
    rw [lookupMapped]
    by_cases yes : (σ,x) ∈ names
    · simp [yes]
    · rw [if_neg yes,support σ x yes]
      exact (literalImage S E H M Γ σ x hw).symm

/-- Instantiate full named application with the finite environment obtained
from the concrete source substitution itself. -/
theorem exact_CanonicalNamedWholeCall
    (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (η : NamedMap) (q : Term) (xs : List Term) (σ τ : Ty) (names : List Name)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (fix : step S E H M = M)
    (hw : WellFormed E.types E.ports Γ)
    (types : ∀ n ∈ names, n.1 ∈ E.types) (support : SupportedNamedMap names η)
    (imageTyping : NamedMapTyped η) (images : FreeImages E H (encodeMap η)) (typed : NamedTyped q σ)
    (covered : Covered E H (encode [] q)) (extra : NamedExtras xs)
    (callTy : CallTyped EmptyContext (encode [] q).type (encodeArgs [] xs) τ)
    (argsCovered : ArgsCovered E H (encodeArgs [] xs)) :
    let a := canonicalValues S E H M (encodeMap η) Γ names
    call S E H M (encode [] q) Γ a [] (domainTypes (encodeArgs [] xs))
      ((evaluateArgs S E H M (encodeArgs [] xs) Γ a []).map Prod.snd) τ =
      concreteOutput S E H M Γ τ
        (apply (encode [] (namedSubstitute η q)) (encodeArgs [] (xs.map (namedSubstitute η)))) := by
  have finite : SupportedFreeMap names (encodeMap η) := by
    intro ρ x hx
    unfold encodeMap
    rw [support ρ x hx]
    rfl
  obtain ⟨valid,related⟩ := exact_CanonicalConcreteEnvironment S E H M (encodeMap η) Γ names
    hc hm hw images types finite
  exact ProtectedSpineNamedConcreteCallProof.exact_NamedFixedConcreteWholeCall
    S E H M Γ η q xs σ τ _ hc hm fix imageTyping images typed covered extra callTy argsCovered valid related

/-- Use the same concrete environment with a finite consumed binder prefix,
leaving the external application arguments outside those binders. -/
theorem exact_CanonicalConcretePrefixCall
    (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q : Expr) (xs consumed : Args) (types : List Ty) (τ : Ty) (names : List Name)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (fix : step S E H M = M)
    (hw : WellFormed E.types E.ports Γ) (namesTyped : ∀ n ∈ names, n.1 ∈ E.types)
    (support : SupportedFreeMap names θ) (images : FreeImages E H θ)
    (bound : BoundImages E H consumed types)
    (typed : Typed (BoundContext.prefix types EmptyContext) q q.type) (covered : Covered E H q)
    (callTy : CallTyped EmptyContext q.type xs τ) (argsCovered : ArgsCovered E H xs) :
    helperWithFree S E H M Γ q xs consumed (canonicalValues S E H M θ Γ names) τ =
      concreteOutput S E H M Γ τ (applyAux (freeSub θ 0 q) (freeSubArgs θ 0 xs) consumed) := by
  obtain ⟨valid,related⟩ := exact_CanonicalConcreteEnvironment S E H M θ Γ names
    hc hm hw images namesTyped support
  exact exact_FixedConcretePrefixCall S E H M Γ θ q xs consumed types τ _
    hc hm fix images bound typed covered callTy argsCovered valid related

#print axioms exact_CanonicalConcreteEnvironment
#print axioms exact_CanonicalNamedWholeCall
#print axioms exact_CanonicalConcretePrefixCall
end LogicLineages.PersistentMarking.ProtectedSpineFiniteConcreteEnvironmentProof
