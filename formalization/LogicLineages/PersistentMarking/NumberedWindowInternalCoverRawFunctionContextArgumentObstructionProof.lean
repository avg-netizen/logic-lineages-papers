module

public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRawFunctionContextArgumentObstructionProof
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowRawContextAlgorithm (next context Frame)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)

/-- No choice of raw witness child can make the actual tag-5 context
branch move between two literal tag-6 parents with different raw args.
This does not restrict the scalar exchange bit or the root-witness branch. -/
theorem exact_RawFunctionContextRejectsChangedArgument (dom cod fn fn' a b witness : Nat)
    (changed : a ≠ b) :
    next 5 [witness] (auxRaw dom cod fn a) (auxRaw dom cod fn' b) = none := by
  unfold next auxRaw
  rw [nodePacked,nodePacked]
  simp [context,changed]

#print axioms exact_RawFunctionContextRejectsChangedArgument
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRawFunctionContextArgumentObstructionProof
