module
public import LogicLineages.OrdinalComparison.ParametricPairWorklistDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode
open ParametricFinitePairCollapse ParametricPairWorklist

def childrenBudget (p : Nat × Nat) (B : Nat) : List (Nat × Nat) :=
  ((List.range (p.1+1)).flatMap (fun a => (List.range (B+1)).map (fun b => (a,b)))).filter
    (fun q => decide (Below q p ∧ pairNorm q≤B))
def query : State → Nat
  | (Sum.inl p::_,_) => pairNorm p
  | _ => 0
def stepBudget (B : Nat) : State → State
  | ([],vs) => ([],vs)
  | (Sum.inl p::ts,vs) =>
      let qs := childrenBudget p B
      (qs.map Sum.inl ++ Sum.inr qs.length::ts,vs)
  | (Sum.inr k::ts,vs) =>
      if k≤vs.length then (ts,combine (vs.take k)::vs.drop k) else (Sum.inr k::ts,vs)
def indexedStep (H : Nat × Nat → Nat) (i : Nat) (s : State) : State :=
  stepBudget (H (i,query s)) s
def indexedRun (H : Nat × Nat → Nat) (i fuel : Nat) (s : State) : State :=
  (indexedStep H i)^[fuel] s
def indexedEvaluate (H : Nat × Nat → Nat) (i : Nat) (p : Nat × Nat) (fuel : Nat) : Option Nat :=
  result (indexedRun H i fuel (initial p))
end LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode
