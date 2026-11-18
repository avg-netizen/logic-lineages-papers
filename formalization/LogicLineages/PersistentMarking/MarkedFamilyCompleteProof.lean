import LogicLineages.PersistentMarking.MarkedFamilyBoundsProof
namespace LogicLineages.PersistentMarking.MarkedFamilyCompleteProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem finiteNonempty : MarkedFamilyLatticeTargets.FiniteNonempty := by
  intro E heads
  constructor
  · exact (FiniteVectorProof.distinct _).filter _
  · exact ⟨MarkedFamilyLattice.join E heads [],(MarkedFamilyBoundsProof.join E heads [] (by intro c h; cases h)).1⟩

theorem complete : MarkedFamilyLatticeTargets.Complete := by
  classical
  intro E heads P
  let cs := (MarkedFamilyCoherence.retained E heads).filter (fun c => decide (P c))
  have hc : ∀ c, c ∈ cs → c ∈ MarkedFamilyCoherence.retained E heads := fun c h => (List.mem_filter.mp h).1
  have hmem : ∀ c, c ∈ MarkedFamilyCoherence.retained E heads → P c → c ∈ cs := by
    intro c h hp; exact List.mem_filter.mpr ⟨h,by simpa using hp⟩
  have j := MarkedFamilyBoundsProof.join E heads cs hc
  have m := MarkedFamilyBoundsProof.meet E heads cs hc
  refine ⟨MarkedFamilyLattice.join E heads cs,MarkedFamilyLattice.meet E heads cs,j.1,m.1,?_,?_,?_,?_⟩
  · intro c h hp; exact j.2.1 c (hmem c h hp)
  · intro b hb hu
    apply j.2.2 b hb
    intro c h
    exact hu c (hc c h) (of_decide_eq_true (List.mem_filter.mp h).2)
  · intro c h hp; exact m.2.1 c (hmem c h hp)
  · intro b hb hl
    apply m.2.2 b hb
    intro c h
    exact hl c (hc c h) (of_decide_eq_true (List.mem_filter.mp h).2)
end LogicLineages.PersistentMarking.MarkedFamilyCompleteProof
