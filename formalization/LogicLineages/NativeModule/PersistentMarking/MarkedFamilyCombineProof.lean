module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyAggregateProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyCombineProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem combineSuccess : MarkedFamilyLatticeTargets.CombineSuccess := by
  intro isMeet E heads cs hc
  obtain ⟨c,he,hr,hv⟩ := MarkedFamilyRetentionProof.encodingComplete E heads _
    (MarkedFamilyAggregateProof.aggregateValid isMeet E heads cs hc)
  have hcombine : MarkedFamilyLattice.combine isMeet E heads cs = c := by
    simp only [MarkedFamilyLattice.combine,he,Option.getD_some]
  rw [hcombine]
  exact ⟨he,hr,hv⟩
end LogicLineages.PersistentMarking.MarkedFamilyCombineProof
