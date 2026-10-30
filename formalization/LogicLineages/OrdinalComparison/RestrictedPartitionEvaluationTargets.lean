module

public import LogicLineages.OrdinalComparison.RestrictedPartitionEvaluationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def RestrictedPartitionZeroDegreeCount : Prop :=
  ∀ n : Nat, restrictedPartitionCount 0 n = if n = 0 then 1 else 0

def RestrictedPartitionRowZeroConvention : Prop :=
  ∀ (previous : List Nat) (n : Nat), restrictedPartitionRowEntry 0 previous n = previous.getD n 0

def RestrictedPartitionRowsCorrect : Prop :=
  ∀ bound d : Nat, (restrictedPartitionRows bound d).length = bound + 1 ∧
    ∀ n : Nat, n ≤ bound → (restrictedPartitionRows bound d).getD n 0 = restrictedPartitionCount d n

def RestrictedPartitionEvaluatorExact : Prop :=
  ∀ d n : Nat, restrictedPartitionEval d n = restrictedPartitionCount d n

def PrimitiveRecursivePartitionSteps : Prop :=
  Primrec (fun z : Nat × List Nat × Nat => restrictedPartitionRowEntry z.1 z.2.1 z.2.2) ∧
    Primrec₂ restrictedPartitionRowStep

def PrimitiveRecursivePartitionEvaluator : Prop :=
  Primrec₂ restrictedPartitionRows ∧ Primrec₂ restrictedPartitionEval ∧ Primrec₂ restrictedPartitionCount

end LogicLineages.OrdinalComparison.Targets
