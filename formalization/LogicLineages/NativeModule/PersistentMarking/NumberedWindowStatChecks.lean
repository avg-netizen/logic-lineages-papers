module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowStatReplacementProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowStatChecks
open NumberedWindowStatTargets

theorem exact_ArgsView : ExactArgsView := NumberedWindowStatParsingProof.argsExact
theorem exact_PartitionView : ExactPartitionView := NumberedWindowStatParsingProof.partitionExact
theorem exact_Mark : ExactMark := NumberedWindowStatMarkProof.markExact
theorem exact_Replacement : ExactReplacement := NumberedWindowStatReplacementProof.replacementExact

#print axioms exact_ArgsView
#print axioms exact_PartitionView
#print axioms exact_Mark
#print axioms exact_Replacement

end LogicLineages.PersistentMarking.NumberedWindowStatChecks
