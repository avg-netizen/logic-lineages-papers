module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFreeAddressProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowFreeAddressChecks
open NumberedWindowFreeAddressTargets

theorem exact_FreeAddress : ExactFreeAddress := NumberedWindowFreeAddressProof.freeExact

theorem exact_FreshArrowProbe : ExactFreshArrowProbe := NumberedWindowFreeAddressProof.freshExact

#print axioms exact_FreeAddress
#print axioms exact_FreshArrowProbe

end LogicLineages.PersistentMarking.NumberedWindowFreeAddressChecks
