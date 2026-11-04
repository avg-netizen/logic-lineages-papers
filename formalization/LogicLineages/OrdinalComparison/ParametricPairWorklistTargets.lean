module
public import LogicLineages.OrdinalComparison.ParametricPairWorklistDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Targets
open ParametricFinitePairCollapse

def ExactChildren : Prop := ∀ (G : Nat → Nat) (p : Nat × Nat),
  (children G p).Nodup ∧ (children G p).toFinset=predecessors G p

def ContinuationCalibration : Prop := ∀ (G : Nat → Nat) (p : Nat × Nat)
    (ts : List Task) (vs : List Nat),
  ∃ fuel : Nat, run G fuel (Sum.inl p::ts,vs)=(ts,value G p::vs)

def ExactSuccess : Prop := ∀ (G : Nat → Nat) (p : Nat × Nat),
  (∀ (fuel n : Nat), evaluate G p fuel=some n → n=value G p) ∧
  (∃ fuel : Nat, evaluate G p fuel=some (value G p)) ∧
  (∃ fuel : Nat, fuel ∈ firstFuel G p ∧ evaluate G p fuel=some (value G p) ∧
    ∀ k<fuel, evaluate G p k=none)
end LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Targets
