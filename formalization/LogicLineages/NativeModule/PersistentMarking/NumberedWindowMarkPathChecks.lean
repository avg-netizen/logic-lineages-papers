module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowMarkPathPrimitiveProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowMarkPathChecks
open NumberedWindowMarkPathTargets

theorem exact_FiniteLoweringChain : FiniteLoweringChain :=
  NumberedWindowMarkPathFiniteProof.finite

theorem exact_ArbitraryMarkDecreasePath : ArbitraryMarkDecreasePath :=
  NumberedWindowMarkPathPrimitiveProof.primitive

#print axioms exact_FiniteLoweringChain
#print axioms exact_ArbitraryMarkDecreasePath

end LogicLineages.PersistentMarking.NumberedWindowMarkPathChecks
