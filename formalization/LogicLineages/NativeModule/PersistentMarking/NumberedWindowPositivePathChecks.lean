module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPositivePathProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathChecks
open NumberedWindowPositivePathTargets

theorem exact_PositivePath : ExactPositivePath := NumberedWindowPositivePathProof.positiveExact
theorem exact_AddressRS : ExactAddressRS := NumberedWindowPositivePathProof.addressExact

#print axioms exact_PositivePath
#print axioms exact_AddressRS

end LogicLineages.PersistentMarking.NumberedWindowPositivePathChecks
