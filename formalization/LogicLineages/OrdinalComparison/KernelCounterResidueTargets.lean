module

public import LogicLineages.OrdinalComparison.KernelCounterResidueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualKernelCounterCongruence : Prop :=
  ∀ d c m : Nat, 1 ≤ d → 1 ≤ m → ∀ t : Nat, kernelCounterThreshold d c m ≤ t →
    Nat.ModEq m (actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t)
      (restrictedPartitionCount d (kernelModularDifference (restrictedPartitionPeriod d m)
        (fastControlResidue (restrictedPartitionPeriod d m)) c))

def PrimitiveRecursiveKernelArithmetic : Prop :=
  Primrec₂ restrictedPartitionPeriod ∧
    Primrec (fun z : Nat × Nat × Nat => kernelModularDifference z.1 z.2.1 z.2.2)

def PrimitiveRecursiveKernelResidue : Prop :=
  Primrec (fun z : Nat × Nat × Nat => kernelCounterResidue z.1 z.2.1 z.2.2) ∧
    Primrec (fun z : Nat × Nat × Nat => kernelCounterThreshold z.1 z.2.1 z.2.2)

def EffectiveActualKernelCounterResidue : Prop :=
  ∀ d c m : Nat, 1 ≤ d → 1 ≤ m →
    kernelCounterResidue d c m < m ∧
      ∀ t : Nat, kernelCounterThreshold d c m ≤ t →
        actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t % m = kernelCounterResidue d c m

end LogicLineages.OrdinalComparison.Targets
