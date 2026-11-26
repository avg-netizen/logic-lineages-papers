import LogicLineages.PersistentMarking.HereditaryRestrictionProof
import LogicLineages.PersistentMarking.HereditaryEncodedRetentionProof
import LogicLineages.PersistentMarking.HereditarySemanticReconstructionProof
namespace LogicLineages.PersistentMarking.HereditaryEncodeDecodeProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem lowerRestriction (E : Environment) (σ : Ty) : HereditaryEncodingTargets.LowerRestriction E σ := by
  intro ρ hsmall Δ Θ hΔ hΘ he c hc
  exact (HereditaryRestrictionProof.restriction E ρ Δ Θ hΔ hΘ he c hc).1

theorem encodeDecode : HereditaryDomainTargets.EncodeDecode := by
  intro E σ Γ v hΓ hvalid
  exact ⟨HereditaryEncodedRetentionProof.retained E σ Γ v hΓ (lowerRestriction E σ) hvalid,
    HereditarySemanticReconstructionProof.reconstruct E σ Γ v hvalid⟩

end LogicLineages.PersistentMarking.HereditaryEncodeDecodeProof
