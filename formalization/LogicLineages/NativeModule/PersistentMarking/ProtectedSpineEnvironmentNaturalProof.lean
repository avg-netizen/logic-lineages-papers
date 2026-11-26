module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineEnvironmentLookupProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineEnvironmentNaturalProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineEnvironmentTargets

theorem literalNatural (E : Environment) (σ : Ty) (Γ Δ : Context) (x : Nat)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    (descriptor E σ).restrict Γ Δ (literalCode E Γ σ x) = literalCode E Δ σ x := by
  have hvalid := MarkedConstructorLiteralProof.literalValid E σ Γ x
  have hΓ := HereditaryEncodeDecodeProof.encodeDecode E σ Γ (literal E σ x) hw hvalid
  have hΔ := HereditaryEncodeDecodeProof.encodeDecode E σ Δ (literal E σ x) hd
    (MarkedConstructorLiteralProof.literalValid E σ Δ x)
  have hr := HereditaryRestrictionProof.restriction E σ Γ Δ hw hd he _ hΓ.1
  exact HereditaryEncodingCongruenceProof.injective E σ Δ _ _ hr.1 hΔ.1
    (HereditaryValueEqualityProof.trans hr.2
      (HereditaryValueEqualityProof.trans (HereditaryValueEqualityProof.weaken he hΓ.2)
        (HereditaryValueEqualityProof.symm hΔ.2)))

theorem bottomNatural (E : Environment) (σ : Ty) (Γ Δ : Context)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    (descriptor E σ).restrict Γ Δ (StructuralActions.bottom E σ Γ) = StructuralActions.bottom E σ Δ :=
  (HereditaryLatticeInductionProof.restriction E σ Γ Δ [] hw hd he (by simp)).1

theorem weakenLookupFree (E : Environment) (Γ Δ : Context) (free : FreeValues) (n : Name) :
    lookupFree (weakenFree E Γ Δ free) n = (lookupFree free n).map ((descriptor E n.1).restrict Γ Δ) := by
  induction free with
  | nil => rfl
  | cons a free ih =>
    obtain ⟨m,c⟩ := a
    by_cases he : m = n
    · subst m
      simp [weakenFree,lookupFree]
    · simpa [weakenFree,lookupFree,he] using ih

theorem weakenLookupBound (E : Environment) (Γ Δ : Context) (bound : BoundValues) (σ : Ty) (i : Nat) :
    lookupBound (weakenBound E Γ Δ bound) σ i = (lookupBound bound σ i).map ((descriptor E σ).restrict Γ Δ) := by
  cases hi : bound[i]? with
  | none => simp [weakenBound,lookupBound,hi]
  | some p =>
    obtain ⟨ρ,c⟩ := p
    by_cases he : ρ = σ
    · subst ρ
      simp [weakenBound,lookupBound,hi]
    · simp [weakenBound,lookupBound,hi,he]

theorem lookupWeakening : LookupWeakening := by
  intro E Γ Δ free bound σ x i hw hd he hf hb
  constructor
  · unfold freeCode
    rw [weakenLookupFree E Γ Δ free (σ,x)]
    cases h : lookupFree free (σ,x) with
    | none => exact literalNatural E σ Γ Δ x hw hd he
    | some c => rfl
  · unfold boundCode
    rw [weakenLookupBound E Γ Δ bound σ i]
    cases h : lookupBound bound σ i with
    | none => exact bottomNatural E σ Γ Δ hw hd he
    | some c => rfl

theorem exact_LookupWeakening : LookupWeakening := lookupWeakening
#print axioms exact_LookupWeakening
end LogicLineages.PersistentMarking.ProtectedSpineEnvironmentNaturalProof
