module
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourcePrimitiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourcePrimitive.Targets

def UniformPrimitiveRecursive : Prop := ∀ H : Nat × Nat → Nat,
  Primrec H → (∀ i : Nat,StrictMono (fun n => H (i,n))) →
  (∀ i n : Nat,n≤H (i,n)) →
  Primrec (fun p : (Nat × Nat) × (Nat × List Nat) =>
    ParametricRestrictedSourceEvaluator.evaluate H p.1.1 p.1.2 p.2.1 p.2.2)

def FixedGammaPrimitive : Prop := ∀ b : Nat,
  Primrec (fun p : Nat × (Nat × List Nat) =>
    ParametricRestrictedSourceEvaluator.gammaEvaluate b p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourcePrimitive.Targets
