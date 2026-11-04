module
public import LogicLineages.OrdinalComparison.ParametricPairValuePrimitiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive.Targets

def ExactCalibration : Prop := ∀ H : Nat × Nat → Nat,
  (∀ i : Nat,StrictMono (fun n => H (i,n))) → (∀ i n : Nat,n≤H (i,n)) →
  ∀ p : Nat × (Nat × Nat),
    ParametricPairCollapseComputable.actualValue H p=iterateValue H p

def UniformPrimitiveRecursive : Prop :=
  (∀ H : Nat × Nat → Nat,Primrec H → Primrec (iterateValue H)) ∧
  (∀ H : Nat × Nat → Nat,Primrec H →
    (∀ i : Nat,StrictMono (fun n => H (i,n))) → (∀ i n : Nat,n≤H (i,n)) →
    Primrec (ParametricPairCollapseComputable.actualValue H))

def FixedGammaPrimitive : Prop := ∀ b : Nat,
  Primrec (ParametricFinitePairCollapse.value (SourceMachineControlNonperiodicity.gamma b))
end LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive.Targets
