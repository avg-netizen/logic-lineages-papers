module
public import LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputsTargets
import LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputsProof
import LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocationSemanticProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListAssignmentsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputs
open ArbitraryHeadFreshWireAllocation (allocate exactAllocatedWireNormalization)
open ArbitraryHeadWireList (extend extendAgrees)

theorem exactCanonicalHiddenAfterOutputs : ExactCanonicalHiddenAfterOutputs := by
  intro f known wires top base final
  have outputs := exactSequentialOutputs f known wires top base final
  have hidden := exactAllocatedWireNormalization f wires final
  constructor
  · exact outputs.trans ⟨fun h => ⟨h.2,hidden.2.1.mpr h.1⟩,
      fun h => ⟨hidden.2.1.mp h.2,h.1⟩⟩
  · intro success
    exact ⟨((hidden.1 (extend final (allocate wires))).mpr ⟨(outputs.mp success).1,rfl⟩).1,
      extendAgrees (allocate wires) final,hidden.2.2⟩

end LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputs
