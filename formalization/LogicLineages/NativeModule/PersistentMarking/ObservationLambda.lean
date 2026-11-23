module

public import LogicLineages.NativeModule.PersistentMarking.DecisionObservations

@[expose] public section

namespace LogicLineages.PersistentMarking.ObservationLambda
open Spine NameBridge DecisionPorts

def firstUnused : Context → Option Nat
  | [] => none
  | none::_ => some 0
  | some _::rest => (firstUnused rest).map (·+1)
def fillSlot : Context → Nat → Ty → Context
  | [], _, _ => []
  | _::rest, 0, σ => some σ :: rest
  | entry::rest, i+1, σ => entry :: fillSlot rest i σ

def FreeValues (vs : Args) : Prop := ∀ i v, vs.get i = some v → ∃ σ x, v = Expr.free σ x
end LogicLineages.PersistentMarking.ObservationLambda
