module

public import LogicLineages.OrdinalComparison.KernelCounterCalibrationDefinitions
public import LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def kernelCounterResidue (d c m : Nat) : Nat :=
  restrictedPartitionEval d (kernelModularDifference (restrictedPartitionPeriod d m)
    (fastControlResidue (restrictedPartitionPeriod d m)) c) % m

def kernelCounterThreshold (d c m : Nat) : Nat :=
  max (restrictedPartitionPeriod d m) (c + d + 1)

end LogicLineages.OrdinalComparison
