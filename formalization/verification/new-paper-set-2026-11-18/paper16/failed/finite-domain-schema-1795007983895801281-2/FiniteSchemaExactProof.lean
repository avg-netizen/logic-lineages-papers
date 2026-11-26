import LogicLineages.PersistentMarking.FiniteExtensionProof
import LogicLineages.PersistentMarking.FiniteVectorProof
namespace LogicLineages.PersistentMarking.FiniteSchemaExactProof
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema

theorem localExact : FiniteDomainSchemaTargets.LocalSchemaExact := by
  intro σ lower V B target Δ key bound
  simp only [atContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_flatMap]
  constructor
  · intro h
    rcases h with ((h|h)|h)|h
    · cases h; exact ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩
    · obtain ⟨t,ht,he⟩ := h
      cases he
      exact ⟨rfl,Or.inr (Or.inl ⟨t,((FiniteEqualityProof.observations _).1 t).mp ht,rfl,rfl⟩)⟩
    · obtain ⟨t,ht,he⟩ := h
      cases he
      exact ⟨rfl,Or.inr (Or.inr (Or.inl ⟨t,((FiniteEqualityProof.observations _).1 t).mp ht,rfl,rfl⟩))⟩
    · obtain ⟨⟨⟨ds,τ⟩,hp⟩,hm,tuple,hv,he⟩ := h
      cases he
      exact ⟨rfl,Or.inr (Or.inr (Or.inr ⟨ds,τ,hp,tuple,(FiniteVectorProof.exactVector _ _).mp hv,rfl,rfl⟩))⟩
  · rintro ⟨hk,h⟩
    cases key with
    | mk context kind =>
      simp only [Key.context] at hk
      subst context
      rcases h with ⟨hk,hb⟩|⟨t,ht,hk,hb⟩|⟨t,ht,hk,hb⟩|⟨ds,τ,hp,tuple,hv,hk,hb⟩
      · cases hk; cases hb; exact Or.inl (Or.inl (Or.inl rfl))
      · cases hk; cases hb
        exact Or.inl (Or.inl (Or.inr ⟨t,((FiniteEqualityProof.observations _).1 t).mpr ht,rfl⟩))
      · cases hk; cases hb
        exact Or.inl (Or.inr ⟨t,((FiniteEqualityProof.observations _).1 t).mpr ht,rfl⟩)
      · cases hk; cases hb
        exact Or.inr ⟨⟨(ds,τ),hp⟩,List.mem_attach _ _,tuple,(FiniteVectorProof.exactVector _ _).mpr hv,rfl⟩

theorem exactSchema : FiniteDomainSchemaTargets.SchemaExact := by
  intro σ lower K V B target Γ key bound
  simp only [schema,List.mem_flatMap]
  constructor
  · rintro ⟨Δ,hΔ,hk⟩
    obtain ⟨hw,he⟩ := (FiniteExtensionProof.enumeration K B Γ Δ).mp hΔ
    exact ⟨Δ,hw,he,(localExact σ lower V B target Δ key bound).mp hk⟩
  · rintro ⟨Δ,hw,he,hk⟩
    exact ⟨Δ,(FiniteExtensionProof.enumeration K B Γ Δ).mpr ⟨hw,he⟩,
      (localExact σ lower V B target Δ key bound).mpr hk⟩

theorem restrictionKeys : FiniteDomainSchemaTargets.RestrictionKeys := by
  intro σ lower K V B target Γ Θ he key bound hk
  obtain ⟨Δ,hw,he',hk⟩ := (exactSchema σ lower K V B target Θ key bound).mp hk
  exact (exactSchema σ lower K V B target Γ key bound).mpr
    ⟨Δ,hw,DecisionPortsProof.extensionTrans Γ Θ Δ he he',hk⟩

theorem rawExact : FiniteDomainSchemaTargets.RawCodeExact := by
  intro σ lower K V B target Γ code
  exact FiniteVectorProof.exactVector _ code

theorem rawDistinct : FiniteDomainSchemaTargets.RawCodeDistinct := by
  intro σ lower K V B target Γ
  exact FiniteVectorProof.distinct _
end LogicLineages.PersistentMarking.FiniteSchemaExactProof
