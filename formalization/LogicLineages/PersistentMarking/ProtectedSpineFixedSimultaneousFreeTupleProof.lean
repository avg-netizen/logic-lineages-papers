import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeCallTargets
import LogicLineages.PersistentMarking.ProtectedSpineFreeSubstitutionProof
import LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
import LogicLineages.PersistentMarking.FreeTypingProof
import LogicLineages.PersistentMarking.FreeCallProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeTupleProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineFreeCases (ArgsSub)
open MarkedConstructorTargets (PrefixClosed)

private theorem argsAgreement (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (θ : FreeMap) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (images : FreeImages E H θ) (xs : Args) : ArgsSub S E H M θ xs := by
  cases xs with
  | nil => exact ProtectedSpineFreeCases.nil S E H M θ
  | cons q rest =>
    exact ProtectedSpineFreeCases.cons S E H M θ images q rest
      (ProtectedSpineFreeSubstitutionProof.expression S E H M θ hc hm images q)
      (argsAgreement S E H M θ hc hm images rest)
termination_by sizeOf xs

/-- The whole ordered list of (type,code) pairs, not only each result bit,
agrees with default interpretation of the actual substituted tuple. -/
theorem exact_FreeImageTupleCodes (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (θ : FreeMap) (a : FreeValues) (xs : Args)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (images : FreeImages E H θ) (typed : ExtrasTyped EmptyContext xs) (covered : ArgsCovered E H xs)
    (valid : InputValid E Γ ⟨a,[]⟩)
    (related : FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩) :
    evaluateArgs S E H M xs Γ a [] = closedCodes S E H M Γ (freeSubArgs θ 0 xs) :=
  argsAgreement S E H M θ hc hm images xs 0 EmptyContext typed covered Γ ⟨a,[]⟩ ⟨[],[]⟩
    valid (ProtectedSpineConcreteInputProof.emptyValid E Γ valid.1) related

theorem exact_FreeImageTupleCallTyped (θ : FreeMap) (hθ : FreeMapTyped EmptyContext θ)
    (σ : Ty) (xs : Args) (τ : Ty) (h : CallTyped EmptyContext σ xs τ) :
    CallTyped EmptyContext σ (freeSubArgs θ 0 xs) τ := by
  induction h with
  | nil => exact .nil
  | cons hx ht ih =>
    exact .cons (FreeTypingProof.freeSubTyped EmptyContext θ hθ _ _ hx) ih

theorem exact_FreeImageTupleDomains (θ : FreeMap) (hθ : FreeMapTyped EmptyContext θ)
    (xs : Args) : domainTypes (freeSubArgs θ 0 xs) = domainTypes xs := by
  cases xs with
  | nil => rfl
  | cons q rest =>
    change (freeSub θ 0 q).type :: domainTypes (freeSubArgs θ 0 rest) = q.type :: domainTypes rest
    rw [FreeCallProof.annotation θ (fun σ x => SpineShiftProof.annotationExact _ _ _ (hθ σ x)),
      exact_FreeImageTupleDomains θ hθ rest]
termination_by sizeOf xs

#print axioms exact_FreeImageTupleCodes
#print axioms exact_FreeImageTupleCallTyped
#print axioms exact_FreeImageTupleDomains
end LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeTupleProof
