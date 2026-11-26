import LogicLineages.PersistentMarking.HereditaryDecodedValidityProof
import LogicLineages.PersistentMarking.HereditaryCodeReconstructionProof
namespace LogicLineages.PersistentMarking.HereditaryDecodeEncodeChecks

theorem exact_DecodeEncode : HereditaryDomainTargets.DecodeEncode := by
  intro E σ Γ c hw hc
  exact ⟨HereditaryDecodedValidityProof.valid E σ Γ c hw hc,
    HereditaryCodeReconstructionProof.reconstruct E σ Γ c hc⟩

#print axioms exact_DecodeEncode
end LogicLineages.PersistentMarking.HereditaryDecodeEncodeChecks
