import LogicLineages.PersistentMarking.ProtectedSpineSoundRelation
import LogicLineages.PersistentMarking.StructuralWholeBottomProof
import LogicLineages.PersistentMarking.HereditaryDecodedValidityProof
import LogicLineages.PersistentMarking.HereditaryCodeOrderProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundRelationProof
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics PortNormalization ProtectedSpineAdequacyTargets
open ProtectedSpineSoundRelation

theorem retained (F : Inputs S) (σ : Ty) (Γ : Context) (c : Code) (r : Option Expr)
    (h : Related F σ Γ c r) : c ∈ (descriptor (domain F) σ).carriers Γ := by
  rw [Related.eq_def] at h
  exact h.1

theorem undefined (F : Inputs S) (σ : Ty) (Γ : Context) (c : Code)
    (h : Related F σ Γ c none) : c = StructuralActions.bottom (domain F) σ Γ := by
  rw [Related.eq_def] at h
  exact h.2

theorem bottomAt (F : Inputs S) (σ : Ty) (Γ : Context) (r : Option Expr)
    (hw : WellFormed F.data.types F.data.ports Γ) :
    Related F σ Γ (StructuralActions.bottom (domain F) σ Γ) r := by
  rw [Related.eq_def]
  have h := StructuralWholeBottomProof.wholeBottom (domain F) σ Γ hw
  refine ⟨h.1,?_⟩
  cases r with
  | none => rfl
  | some q =>
    intro Δ hd he
    obtain ⟨_,hBits,hApp⟩ := h.2 Δ hd he
    constructor
    · intro t ht
      obtain ⟨hWeak,hStrict⟩ := hBits t ht
      exact ⟨fun h => Bool.noConfusion (hWeak.symm.trans h),
        fun h => Bool.noConfusion (hStrict.symm.trans h)⟩
    · intro ds τ hp xs args hx _ _ _
      rw [hApp ds τ hp xs hx]
      exact bottomAt F τ Δ (apply q args) hd
termination_by typeSize σ
decreasing_by exact (FinitePrefixProof.proper _ _ _ ‹_ ∈ _›).1

theorem exact_Bottom : Bottom := fun _ => bottomAt

theorem downwardAt (F : Inputs S) (σ : Ty) (Γ : Context) (a b : Code) (r : Option Expr)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (ha : a ∈ (descriptor (domain F) σ).carriers Γ)
    (hle : (descriptor (domain F) σ).le Γ a b = true) (hb : Related F σ Γ b r) :
    Related F σ Γ a r := by
  rw [Related.eq_def] at hb ⊢
  refine ⟨ha,?_⟩
  cases r with
  | none =>
    have he : b = StructuralActions.bottom (domain F) σ Γ := hb.2
    have hleast := (HereditaryLatticeInductionProof.join (domain F) σ Γ [] hw (by simp)).2.2 a ha (by simp)
    exact (HereditaryPartialOrderProof.partialOrder (domain F) σ Γ hw).2.2 a
      (StructuralActions.bottom (domain F) σ Γ) ha (he ▸ hb.1) (he ▸ hle) hleast
  | some q =>
    have hord := (HereditaryCodeOrderProof.exactOrder (domain F) σ Γ a b hw ha hb.1).mp hle
    have hv := (HereditaryDecodedValidityProof.valid (domain F) σ Γ a hw ha).1
    intro Δ hd he
    obtain ⟨_,hBits,hApp⟩ := hord Δ hd he
    obtain ⟨hSound,hAction⟩ := hb.2 Δ hd he
    refine ⟨?_,?_⟩
    · intro t ht
      exact ⟨(hSound t ht).1 ∘ (hBits t ht).1,(hSound t ht).2 ∘ (hBits t ht).2⟩
    · intro ds τ hp xs args hx hArgs hSource hRelated
      exact downwardAt F τ Δ _ _ _ hd (hv Δ hd he ds τ hp xs hx) (hApp ds τ hp xs hx)
        (hAction ds τ hp xs args hx hArgs hSource hRelated)
termination_by typeSize σ
decreasing_by exact (FinitePrefixProof.proper _ _ _ ‹_ ∈ _›).1

theorem exact_Downward : Downward := fun _ => downwardAt

theorem exact_Restriction : Restriction := by
  intro S F σ Γ Δ c r hw hd he h
  rw [Related.eq_def] at h ⊢
  have hr := HereditaryRestrictionProof.restriction (domain F) σ Γ Δ hw hd he c h.1
  refine ⟨hr.1,?_⟩
  cases r with
  | none =>
    have hc : c = StructuralActions.bottom (domain F) σ Γ := h.2
    subst c
    exact (HereditaryLatticeInductionProof.restriction (domain F) σ Γ Δ [] hw hd he (by simp)).1
  | some q =>
    intro Θ ht hExt
    obtain ⟨_,hBits,hApp⟩ := hr.2 Θ ht hExt
    obtain ⟨hSound,hAction⟩ := h.2 Θ ht (DecisionPortsProof.extensionTrans Γ Δ Θ he hExt)
    constructor
    · intro t hObs
      obtain ⟨hW,hS⟩ := hBits t hObs
      exact ⟨fun h => (hSound t hObs).1 (hW.symm.trans h),fun h => (hSound t hObs).2 (hS.symm.trans h)⟩
    · intro ds τ hp xs args hx hArgs hSource hRelated
      rw [hApp ds τ hp xs hx]
      exact hAction ds τ hp xs args hx hArgs hSource hRelated

#print axioms exact_Bottom
#print axioms exact_Downward
#print axioms exact_Restriction
end LogicLineages.PersistentMarking.ProtectedSpineSoundRelationProof
