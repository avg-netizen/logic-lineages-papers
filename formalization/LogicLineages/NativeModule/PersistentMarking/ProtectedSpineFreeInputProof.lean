module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSubstitutionTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineInterpretationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineFreeInputProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineSubstitutionTargets
open ProtectedSpineEnvironment (freeCode)
open MarkedConstructorTargets (PrefixClosed)

theorem emptyBoundValid (E : Environment) (Γ : Context) (a : Assignments) (ha : InputValid E Γ a) :
    InputValid E Γ ⟨a.free,[]⟩ :=
  ⟨ha.1,ha.2.1,by simp [ProtectedSpineEnvironmentTargets.BoundValid]⟩

theorem weaken (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hθ : FreeImages E H θ)
    (Γ Δ : Context) (a b : Assignments) (ha : InputValid E Γ a) (hb : InputValid E Γ b)
    (hr : FreeSubstitutionInputs S E H M θ Γ a b) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    FreeSubstitutionInputs S E H M θ Δ (a.restrict E Γ Δ) (b.restrict E Γ Δ) := by
  constructor
  · change ProtectedSpineEnvironment.weakenBound E Γ Δ a.bound = ProtectedSpineEnvironment.weakenBound E Γ Δ b.bound
    rw [hr.1]
  · intro σ hσ x
    have hL := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ x 0 ha.1 hd he ha.2.1 ha.2.2).1
    let ev := evaluate S E H M (θ σ x)
    have hl := ProtectedSpineInterpretationProof.laws S E H M hc hm EmptyContext (θ σ x) σ
      (hθ.1 σ x) (hθ.2 σ hσ x)
    have hR := ProtectedSpineEncodingProof.codeNatural E σ ev hl Γ Δ ⟨b.free,[]⟩
      (emptyBoundValid E Γ b hb) hd he
    have hL' := hL.symm
    rw [hr.2 σ hσ x] at hL'
    exact hL'.trans hR

theorem push (S : Signature) (E : Environment) (H : List Head) (M : Code) (θ : FreeMap)
    (Γ : Context) (a b : Assignments) (σ : Ty) (c : Code)
    (h : FreeSubstitutionInputs S E H M θ Γ a b) :
    FreeSubstitutionInputs S E H M θ Γ (a.push σ c) (b.push σ c) :=
  ⟨congrArg ((σ,c)::·) h.1,h.2⟩

end LogicLineages.PersistentMarking.ProtectedSpineFreeInputProof
