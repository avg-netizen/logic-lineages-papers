module

public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionTargets
open OracleRelativeRecursion

def RelativeComposition : Prop :=
  ∀ (O : Set (Nat → Part Nat)) (f g : Nat → Nat), ComputableIn O f → ComputableIn O g →
    ComputableIn O (fun n => f (g n))

def RelativeNumericPairing : Prop :=
  ∀ (O : Set (Nat → Part Nat)) (f g : Nat → Nat), ComputableIn O f → ComputableIn O g →
    ComputableIn O (fun n => Nat.pair (f n) (g n))

def RelativePrimitiveRecursion : Prop :=
  ∀ (O : Set (Nat → Part Nat)) (initial step : Nat → Nat),
    ComputableIn O initial → ComputableIn O step → ComputableIn O (parameterRec initial step)

def RelativePartialSearch : Prop :=
  ∀ (O : Set (Nat → Part Nat)) (test : Nat → Nat), ComputableIn O test →
    RecursiveIn O (zeroSearch test)

end LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionTargets
