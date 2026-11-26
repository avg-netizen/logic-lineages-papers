module
public import LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocationTargets
import LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocationProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListAssignmentsProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListProof

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocation
open ArbitraryHeadWireList
open ArbitraryHeadSharedWire (Valuation)

private theorem exactOriginalConjunction (f : Nat → Nat) (wires : List Wire) (ν : Valuation) :
    OriginalAt f ν (allocate wires) ↔ OriginalConjunction f ν wires := by
  have shape := (exactFreshAllocation wires).1
  constructor
  · intro orig w hw
    rw [← shape] at hw
    obtain ⟨g,hg,he⟩ := List.mem_map.mp hw
    subst w
    exact orig g hg
  · intro orig g hg
    have hm : strip g ∈ wires := by
      rw [← shape]
      exact List.mem_map.mpr ⟨g,hg,rfl⟩
    exact orig (strip g) hm

theorem exactAllocatedWireNormalization : ExactAllocatedWireNormalization := by
  intro f wires ν
  have fresh := (exactFreshAllocation wires).2.1
  have above := (exactFreshAllocation wires).2.2
  have original := exactOriginalConjunction f wires ν
  refine ⟨?_,(uniqueSharedWireList f (allocate wires) fresh ν).1.trans original,?_⟩
  · intro θ
    exact (exactSharedWireList f (allocate wires) fresh ν θ).trans
      (and_congr original Iff.rfl)
  · intro n hn
    exact extendAgrees (allocate wires) ν n (fun mem => (Nat.not_lt_of_ge hn) (above n mem))

end LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocation
