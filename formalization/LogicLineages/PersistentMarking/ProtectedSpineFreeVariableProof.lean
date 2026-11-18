import LogicLineages.PersistentMarking.ProtectedSpineFreeInputProof
import LogicLineages.PersistentMarking.ProtectedSpineScopeAgreementProof
import LogicLineages.PersistentMarking.ProtectedSpineTableProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFreeVariableProof
open Spine FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineAgreementTargets ProtectedSpineSubstitutionTargets
open MarkedConstructorTargets (PrefixClosed)

theorem free (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hθ : FreeImages E H θ)
    (σ : Ty) (x depth : Nat) (hσ : σ ∈ E.types) :
    Agreement E σ (evaluate S E H M (.free σ x)) (evaluate S E H M (freeSub θ depth (.free σ x)))
      (FreeSubstitutionInputs S E H M θ) (· = ·) := by
  have hty := hθ.1 σ x
  have hcov := hθ.2 σ hσ x
  have he : freeSub θ depth (.free σ x) = θ σ x := ClosedSyntaxProof.closedShift (θ σ x) σ hty depth
  rw [he]
  let image := evaluate S E H M (θ σ x)
  have hl := ProtectedSpineInterpretationProof.laws S E H M hc hm EmptyContext (θ σ x) σ hty hcov
  have hag := ProtectedSpineScopeAgreementProof.exact_ScopeAgreement S E H M EmptyContext (θ σ x) σ hty hcov
  have hframe : ∀ Γ b, SameInputs E EmptyContext Γ ⟨b.free,[]⟩ b := by
    intro Γ b
    exact ⟨fun _ _ => rfl,fun _ _ h => by cases h⟩
  constructor
  · intro Γ a b ha hb hr
    let b₀ : Assignments := ⟨b.free,[]⟩
    have hb₀ := ProtectedSpineFreeInputProof.emptyBoundValid E Γ b hb
    change ValueEq E σ Γ (decode E σ Γ (freeCode E Γ a.free σ x)) (valueAt image Γ b)
    rw [hr.2 σ hσ x]
    exact HereditaryValueEqualityProof.trans (ProtectedSpineEncodingProof.encodeAt E σ image hl Γ b₀ hb₀).2
      (hag.value Γ b₀ b hb₀ hb (hframe Γ b))
  · intro Γ a b k l ds τ xs ha hb hr hkl hp hx
    cases hkl
    let b₀ : Assignments := ⟨b.free,[]⟩
    have hb₀ := ProtectedSpineFreeInputProof.emptyBoundValid E Γ b hb
    have hcall := ProtectedSpineVariableProof.callEq E σ (fun Δ p => freeCode E Δ p.free σ x)
      (fun _ => false) Γ a k ds τ xs hp hx
    change nonemptyAt E (evaluate S E H M (.free σ x)) Γ a k ds τ xs =
      nonemptyAt E image Γ b k ds τ xs
    rw [show nonemptyAt E (evaluate S E H M (.free σ x)) Γ a k ds τ xs =
      StructuralActions.fullAction E σ Γ (freeCode E Γ a.free σ x) ds τ xs from hcall,hr.2 σ hσ x]
    have hv := (ProtectedSpineEncodingProof.encodeAt E σ image hl Γ b₀ hb₀).2
    have hApp := (hv Γ hb.1 (DecisionPortsProof.extensionRefl Γ)).2.2 ds τ hp xs hx
    have hTable := ProtectedSpineTableProof.table S E H M EmptyContext (θ σ x) σ hc hm hty hcov Γ b₀ hb₀
      ds τ xs hp hx
    have hAg := hag.call Γ b₀ b 0 k ds τ xs hb₀ hb (hframe Γ b) (by intro _ _ h; cases h) hp hx
    exact hApp.trans (hTable.symm.trans hAg)

end LogicLineages.PersistentMarking.ProtectedSpineFreeVariableProof
