module
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNumericalMatching
def Matching (edge app : Nat → Nat → Nat → Bool) : Prop :=
  ∀ f g u v w, edge f w g = true → app g u v = true →
    ∃ b z, app f u b = true ∧ edge b z v = true
end LogicLineages.PersistentMarking.NumberedWindowNumericalMatching
