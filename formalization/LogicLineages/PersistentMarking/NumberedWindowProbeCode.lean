module
public import LogicLineages.OrdinalComparison.SourceTypes
public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowProbeCode
open LogicLineages.OrdinalComparison.Source
def code : Ty → Nat
  | .ground => 0
  | .arrow σ τ => NumberedWindowPairAlgorithm.pair (code σ) (code τ) + 1

def NumericalTotal (typed : Nat → Nat → Bool) (probe : Nat → Option Nat)
    (app : Nat → Nat → Nat → Bool) : Prop :=
  ∀ (σ τ : Ty) f, typed (code (.arrow σ τ)) f = true →
    ∃ u v, probe f = some u ∧ app f u v = true ∧ typed (code τ) v = true
end LogicLineages.PersistentMarking.NumberedWindowProbeCode
