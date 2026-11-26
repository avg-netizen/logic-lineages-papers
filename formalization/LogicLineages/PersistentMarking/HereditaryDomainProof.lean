import LogicLineages.PersistentMarking.HereditaryLatticeCompleteProof
import LogicLineages.PersistentMarking.HereditaryRestrictionAlgebraProof
namespace LogicLineages.PersistentMarking.HereditaryDomainProof

theorem full : HereditaryDomainTargets.FullFiniteLattices := by
  refine ⟨HereditaryConstructionProof.equation,HereditaryConstructionProof.effective,
    HereditaryConstructionProof.distinct,HereditaryLatticeCompleteProof.nonempty,?_,
    HereditaryEncodeDecodeProof.encodeDecode,HereditaryPartialOrderProof.partialOrder,
    HereditaryLatticeInductionProof.join,HereditaryLatticeInductionProof.meet,
    HereditaryRestrictionProof.restriction,HereditaryRestrictionAlgebraProof.algebra,
    HereditaryLatticeInductionProof.restriction,HereditaryLatticeCompleteProof.complete⟩
  intro E σ Γ c hw hc
  exact ⟨HereditaryDecodedValidityProof.valid E σ Γ c hw hc,
    HereditaryCodeReconstructionProof.reconstruct E σ Γ c hc⟩
end LogicLineages.PersistentMarking.HereditaryDomainProof
