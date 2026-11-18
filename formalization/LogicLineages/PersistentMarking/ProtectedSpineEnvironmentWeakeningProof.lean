import LogicLineages.PersistentMarking.ProtectedSpineEnvironmentTargets
import LogicLineages.PersistentMarking.HereditaryRestrictionAlgebraProof
import LogicLineages.PersistentMarking.HereditaryRestrictionProof

namespace LogicLineages.PersistentMarking.ProtectedSpineEnvironmentWeakeningProof
open Spine DecisionPorts HereditaryDomainCode ProtectedSpineEnvironment ProtectedSpineEnvironmentTargets

theorem freeWeakening (E : Environment) (Γ Δ : Context) (free : FreeValues)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hf : FreeValid E Γ free) : FreeValid E Δ (weakenFree E Γ Δ free) := by
  intro a ha
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
  exact (HereditaryRestrictionProof.restriction E p.1.1 Γ Δ hw hd he p.2 (hf p hp)).1

theorem boundWeakening (E : Environment) (Γ Δ : Context) (bound : BoundValues)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hb : BoundValid E Γ bound) : BoundValid E Δ (weakenBound E Γ Δ bound) := by
  intro a ha
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
  exact (HereditaryRestrictionProof.restriction E p.1 Γ Δ hw hd he p.2 (hb p hp)).1

theorem weakening : Weakening := by
  intro E Γ Δ free bound hw hd he hf hb
  exact ⟨freeWeakening E Γ Δ free hw hd he hf,boundWeakening E Γ Δ bound hw hd he hb⟩

theorem composition : EnvironmentComposition := by
  intro E Γ Δ Θ free bound hw hd ht he hExt hf hb
  constructor
  · simp only [weakenFree,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro a ha
    rw [(HereditaryRestrictionAlgebraProof.algebra E a.1.1).2 Γ Δ Θ a.2 hw hd ht he hExt (hf a ha)]
  · simp only [weakenBound,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro a ha
    rw [(HereditaryRestrictionAlgebraProof.algebra E a.1).2 Γ Δ Θ a.2 hw hd ht he hExt (hb a ha)]

theorem pushValid (E : Environment) (Γ : Context) (bound : BoundValues) (σ : Ty) (c : FiniteDomainSchema.Code)
    (hb : BoundValid E Γ bound) (hc : c ∈ (descriptor E σ).carriers Γ) :
    BoundValid E Γ ((σ,c)::bound) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hc
  · exact hb a ha

theorem exact_Weakening : Weakening := weakening
theorem exact_EnvironmentComposition : EnvironmentComposition := composition
#print axioms exact_Weakening
#print axioms exact_EnvironmentComposition
end LogicLineages.PersistentMarking.ProtectedSpineEnvironmentWeakeningProof
