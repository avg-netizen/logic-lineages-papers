import LogicLineages.PersistentMarking.HereditaryCodeReconstructionProof
namespace LogicLineages.PersistentMarking.HereditaryCodeReconstructionChecks
open HereditaryDomainCode HereditaryDomainSemantics

theorem exact_CodeReconstruction : ∀ E σ Γ c,
    c ∈ (descriptor E σ).carriers Γ → encode E σ Γ (HereditaryDomainSemantics.decode E σ Γ c) = c :=
  HereditaryCodeReconstructionProof.reconstruct
#print axioms exact_CodeReconstruction
end LogicLineages.PersistentMarking.HereditaryCodeReconstructionChecks
