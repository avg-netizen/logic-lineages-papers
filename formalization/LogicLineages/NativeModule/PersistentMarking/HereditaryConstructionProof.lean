module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryDomainTargets
public import LogicLineages.NativeModule.PersistentMarking.FiniteSchemaExactProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryConstructionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem equation : HereditaryDomainTargets.ConstructionEquation := by
  intro E σ
  rw [descriptor]
  rfl

theorem effective : HereditaryDomainTargets.EffectiveCarrier := by
  intro E σ Γ c
  rw [equation E σ]
  change c ∈ (rawCodes σ (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ).filter
    (fun c => monotone E σ (canonicalLower E σ) Γ c && natural E σ (canonicalLower E σ) Γ c) ↔ _
  rw [List.mem_filter,FiniteSchemaExactProof.rawExact]
  simp only [Bool.and_eq_true]
  rfl

theorem distinct : HereditaryDomainTargets.CarrierDistinct := by
  intro E σ Γ
  rw [equation E σ]
  exact (FiniteSchemaExactProof.rawDistinct σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ).filter _
end LogicLineages.PersistentMarking.HereditaryConstructionProof
