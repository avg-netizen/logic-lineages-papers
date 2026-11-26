import LogicLineages.PersistentMarking.MarkedFamilyCombineProof
namespace LogicLineages.PersistentMarking.MarkedFamilyBoundsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem join : MarkedFamilyLatticeTargets.Join := by
  intro E heads cs hc
  have hcomb := MarkedFamilyCombineProof.combineSuccess false E heads cs hc
  have hr : MarkedFamilyLattice.join E heads cs ∈ MarkedFamilyCoherence.retained E heads := hcomb.2.1
  have he := hcomb.2.2
  refine ⟨hr,?_,?_⟩
  · intro c hcs
    apply (MarkedFamilyOrderProof.orderExact E heads c _ (hc c hcs) hr).mpr
    intro p hp
    change (descriptor E p.2.1).le p.2.2.1 (MarkedFamilyCoding.decode E heads c p)
      (MarkedFamilyCoding.decode E heads (MarkedFamilyLattice.combine false E heads cs) p) = true
    rw [he p hp]
    exact (HereditaryLatticeInductionProof.join E p.2.1 p.2.2.1 _ hp.2.2.1
      (MarkedFamilyAggregateProof.members E heads cs hc p hp)).2.1 _ (List.mem_map.mpr ⟨c,hcs,rfl⟩)
  · intro b hb hu
    apply (MarkedFamilyOrderProof.orderExact E heads _ b hr hb).mpr
    intro p hp
    change (descriptor E p.2.1).le p.2.2.1
      (MarkedFamilyCoding.decode E heads (MarkedFamilyLattice.combine false E heads cs) p)
      (MarkedFamilyCoding.decode E heads b p) = true
    rw [he p hp]
    apply (HereditaryLatticeInductionProof.join E p.2.1 p.2.2.1 _ hp.2.2.1
      (MarkedFamilyAggregateProof.members E heads cs hc p hp)).2.2 _
      (((MarkedFamilyRetentionProof.retentionExact E heads b).mp hb).2.1 p hp)
    intro x hx
    obtain ⟨c,hcs,rfl⟩ := List.mem_map.mp hx
    exact (MarkedFamilyOrderProof.orderExact E heads c b (hc c hcs) hb).mp (hu c hcs) p hp

theorem meet : MarkedFamilyLatticeTargets.Meet := by
  intro E heads cs hc
  have hcomb := MarkedFamilyCombineProof.combineSuccess true E heads cs hc
  have hr : MarkedFamilyLattice.meet E heads cs ∈ MarkedFamilyCoherence.retained E heads := hcomb.2.1
  have he := hcomb.2.2
  refine ⟨hr,?_,?_⟩
  · intro c hcs
    apply (MarkedFamilyOrderProof.orderExact E heads _ c hr (hc c hcs)).mpr
    intro p hp
    change (descriptor E p.2.1).le p.2.2.1
      (MarkedFamilyCoding.decode E heads (MarkedFamilyLattice.combine true E heads cs) p)
      (MarkedFamilyCoding.decode E heads c p) = true
    rw [he p hp]
    exact (HereditaryLatticeInductionProof.meet E p.2.1 p.2.2.1 _ hp.2.2.1
      (MarkedFamilyAggregateProof.members E heads cs hc p hp)).2.1 _ (List.mem_map.mpr ⟨c,hcs,rfl⟩)
  · intro b hb hl
    apply (MarkedFamilyOrderProof.orderExact E heads b _ hb hr).mpr
    intro p hp
    change (descriptor E p.2.1).le p.2.2.1 (MarkedFamilyCoding.decode E heads b p)
      (MarkedFamilyCoding.decode E heads (MarkedFamilyLattice.combine true E heads cs) p) = true
    rw [he p hp]
    apply (HereditaryLatticeInductionProof.meet E p.2.1 p.2.2.1 _ hp.2.2.1
      (MarkedFamilyAggregateProof.members E heads cs hc p hp)).2.2 _
      (((MarkedFamilyRetentionProof.retentionExact E heads b).mp hb).2.1 p hp)
    intro x hx
    obtain ⟨c,hcs,rfl⟩ := List.mem_map.mp hx
    exact (MarkedFamilyOrderProof.orderExact E heads b c hb (hc c hcs)).mp (hl c hcs) p hp
end LogicLineages.PersistentMarking.MarkedFamilyBoundsProof
