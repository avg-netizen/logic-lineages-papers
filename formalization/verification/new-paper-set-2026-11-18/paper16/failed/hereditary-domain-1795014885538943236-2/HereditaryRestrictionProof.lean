import LogicLineages.PersistentMarking.HereditaryProjectionRetentionProof
import LogicLineages.PersistentMarking.HereditaryProjectionSemanticsProof
namespace LogicLineages.PersistentMarking.HereditaryRestrictionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem restriction : HereditaryDomainTargets.Restriction := by
  intro E σ Γ Θ hΓ hΘ he c hc
  have hr := HereditaryProjectionRetentionProof.retained E σ Γ Θ c he hc
  have hs := HereditaryProjectionSemanticsProof.semantics E σ Γ Θ c he hc
  have hdef : (descriptor E σ).restrict Γ Θ c = project E σ (canonicalLower E σ) Γ Θ c := by
    rw [HereditaryConstructionProof.equation E σ]
    rfl
  rw [hdef]
  exact ⟨hr,hs⟩

end LogicLineages.PersistentMarking.HereditaryRestrictionProof
