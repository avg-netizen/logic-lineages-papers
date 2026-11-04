module
public import LogicLineages.OrdinalComparison.ParametricPairMachineCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Targets
open ParametricFinitePairCollapse ParametricPairWorklist

def ExactCalibration : Prop := ∀ H : Nat × Nat → Nat,
  (∀ i p, childrenBudget p (H (i,pairNorm p))=children (fun n => H (i,n)) p) ∧
  (∀ i s, indexedStep H i s=step (fun n => H (i,n)) s) ∧
  (∀ i fuel s, indexedRun H i fuel s=run (fun n => H (i,n)) fuel s) ∧
  (∀ i p fuel, indexedEvaluate H i p fuel=evaluate (fun n => H (i,n)) p fuel)

def KernelPrimitiveRecursive : Prop :=
  Primrec (fun p : (Nat × Nat) × Nat => childrenBudget p.1 p.2) ∧
  Primrec query ∧ Primrec (fun p : Nat × State => stepBudget p.1 p.2) ∧ Primrec result

def IndexedPrimitiveRecursive : Prop := ∀ H : Nat × Nat → Nat, Primrec H →
  Primrec (fun p : Nat × State => indexedStep H p.1 p.2) ∧
  Primrec (fun p : (Nat × Nat) × State => indexedRun H p.1.1 p.1.2 p.2) ∧
  Primrec (fun p : (Nat × (Nat × Nat)) × Nat => indexedEvaluate H p.1.1 p.1.2 p.2)

def IndexedComputable : Prop := ∀ H : Nat × Nat → Nat, Computable H →
  Computable (fun p : Nat × State => indexedStep H p.1 p.2) ∧
  Computable (fun p : (Nat × Nat) × State => indexedRun H p.1.1 p.1.2 p.2) ∧
  Computable (fun p : (Nat × (Nat × Nat)) × Nat => indexedEvaluate H p.1.1 p.1.2 p.2)
end LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Targets
