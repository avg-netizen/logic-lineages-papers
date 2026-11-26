module
public import LogicLineages.StandardControlCurrent.NumericalKernelDefinitions
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.Definitions
public import LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.KernelResiduesTargets
open OrdinalComparison NumericalKernel KernelSourceCompletion

def CounterResidue : Prop := ∀ d c m : Nat, 1 ≤ d → 1 ≤ m →
  kernelCounterResidue d c m < m ∧ ∀ t : Nat, kernelCounterThreshold d c m ≤ t →
    count d c t % m = kernelCounterResidue d c m ∧
    Nat.ModEq m (count d c t)
      (restrictedPartitionCount d (kernelModularDifference (restrictedPartitionPeriod d m)
        (fastControlResidue (restrictedPartitionPeriod d m)) c))

def SignedResidue : Prop := ∀ d c : Nat, ∀ j : Int, admissibleSignedPair d j →
  ∀ m : Nat, 1 ≤ m → ∀ t : Nat, correctedSignedKernelThreshold d c j m ≤ t →
    0 < depth d c j t ∧ Nat.ModEq m (signed d c j t) (fastControlResidue m)

def PaddedTail : Prop := ∀ d c m : Nat, 1 ≤ d → 1 ≤ m → ∀ t : Nat,
  kernelCounterThreshold d c m ≤ t → c+d+1 ≤ t ∧
    count d c t = actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
    value d c t = actualSuffixKernel (Ordinal.omega0 ^ (d : Ordinal)) c t

def BudgetResidues : Prop := ∀ d c m : Nat, 1 ≤ d → 1 ≤ m → ∀ t : Nat,
  kernelCounterThreshold d c m ≤ t → ∀ i : Nat,
    (Phi^[i]) t < (Phi^[i+1]) t ∧ c ≤ (Phi^[i+1]) t ∧
    Nat.ModEq (restrictedPartitionPeriod d m) ((Phi^[i+1]) t)
      (fastControlResidue (restrictedPartitionPeriod d m))

def ModularCalibration : Prop :=
  (∀ d m : Nat, 1 ≤ d → 1 ≤ m → 0 < restrictedPartitionPeriod d m ∧
    fastControlResidue (restrictedPartitionPeriod d m) < restrictedPartitionPeriod d m) ∧
  (∀ Q r c : Nat, 0 < Q → r < Q → kernelModularDifference Q r c < Q ∧
    ∀ S : Nat, c ≤ S → Nat.ModEq Q S r →
      Nat.ModEq Q (S-c) (kernelModularDifference Q r c)) ∧
  (∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ a b : Nat,
    Nat.ModEq (restrictedPartitionPeriod d m) a b →
      Nat.ModEq m (restrictedPartitionCount d a) (restrictedPartitionCount d b))

def PartitionAlgorithm : Prop :=
  (∀ d n : Nat, restrictedPartitionEval d n = restrictedPartitionCount d n) ∧
  Primrec₂ restrictedPartitionEval ∧ Primrec₂ restrictedPartitionPeriod ∧
  Primrec (fun x : Nat × Nat × Nat => kernelModularDifference x.1 x.2.1 x.2.2)

def Programs : Prop :=
  Primrec (fun x : Nat × Nat × Nat => kernelCounterResidue x.1 x.2.1 x.2.2) ∧
  Primrec (fun x : Nat × Nat × Nat => kernelCounterThreshold x.1 x.2.1 x.2.2) ∧
  (∀ j : Int, Primrec (fun x : Nat × Nat × Nat => correctedSignedKernelThreshold x.1 x.2.1 j x.2.2)) ∧
  Primrec fastControlResidue

def Full : Prop := CounterResidue ∧ SignedResidue ∧ PaddedTail ∧ BudgetResidues ∧
  ModularCalibration ∧ PartitionAlgorithm ∧ Programs
end LogicLineages.StandardControlCurrent.KernelResiduesTargets
