module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreePrimitiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreePrimitive.Targets

def UniformPrimitiveRecursive : Prop := ∀ H : Nat × Nat → Nat,
  Primrec H → (∀ i : Nat,StrictMono (fun n => H (i,n))) →
  (∀ i n : Nat,n≤H (i,n)) →
  Primrec (fun p : (Nat × List Nat) × Nat =>
    ParametricOmegaFreeEvaluator.evaluate H p.1.1 p.1.2 p.2)

def FixedGammaPrimitive : Prop := ∀ b : Nat,
  Primrec (fun p : List Nat × Nat => ParametricOmegaFreeEvaluator.evaluate
    (fun q : Nat × Nat => SourceMachineControlNonperiodicity.gamma b q.2) 0 p.1 p.2)
end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreePrimitive.Targets
