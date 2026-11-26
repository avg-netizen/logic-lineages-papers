module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalStepLambdaProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalStepLambdaChecks
open NativeOrdinalStepLambdaTargets NativeOrdinalStepLambdaProof

theorem exact_MultiplicationStepLambdaBeta : MultiplicationStepLambdaBeta :=
  multiplicationStepBeta

theorem exact_PowerStepLambdaBeta : PowerStepLambdaBeta :=
  powerStepBeta

#print axioms exact_MultiplicationStepLambdaBeta
#print axioms exact_PowerStepLambdaBeta

end LogicLineages.PersistentMarking.NativeOrdinalStepLambdaChecks
