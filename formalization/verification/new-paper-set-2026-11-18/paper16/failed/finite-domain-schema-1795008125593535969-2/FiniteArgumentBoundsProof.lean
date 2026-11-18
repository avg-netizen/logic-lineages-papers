import LogicLineages.PersistentMarking.FiniteDomainSchemaTargets
namespace LogicLineages.PersistentMarking.FiniteArgumentBoundsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema

theorem coordinates : FiniteDomainSchemaTargets.ArgumentBoundCoordinates := by
  intro σ lower Δ domains τ h
  refine ⟨by simp [argumentBounds],?_⟩
  intro i ρ hi
  have hm : ρ ∈ domains := List.mem_of_getElem? hi
  let hp := (FinitePrefixProof.proper σ domains τ h).2 ρ hm
  refine ⟨hp,?_⟩
  simp only [argumentBounds,List.getElem?_map,List.getElem?_attach]
  simp [hi]
end LogicLineages.PersistentMarking.FiniteArgumentBoundsProof
