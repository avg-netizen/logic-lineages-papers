module

public import LogicLineages.NativeModule.PersistentMarking.StructuralActionTargets
public import LogicLineages.NativeModule.PersistentMarking.HereditaryLatticeInductionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralWholeBottomProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem wholeBottom : StructuralActionTargets.WholeBottom := by
  intro E σ Γ hw
  have h := HereditaryLatticeClosureProof.closure E σ Γ false [] hw
    (fun ρ _ => HereditaryLatticeInductionProof.lattice E ρ)
    (by intro c hc; cases hc)
  refine ⟨h.1, ?_⟩
  intro Δ hd he
  have eq := h.2 Δ hd he
  exact eq
end LogicLineages.PersistentMarking.StructuralWholeBottomProof
