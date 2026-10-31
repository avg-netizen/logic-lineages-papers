module
public import Mathlib.Computability.StateTransition
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAttachExit

/-- Run the first system until its next step is `none`, then take exactly one
bridge transition into the second system at `exit` of that terminal state.
The bridge is taken even when the second entry state is already terminal. -/
def step {α β : Type} (f : α → Option α) (g : β → Option β) (exit : α → β) :
    α ⊕ β → Option (α ⊕ β)
  | .inl a => match f a with
    | some a' => some (.inl a')
    | none => some (.inr (exit a))
  | .inr b => (g b).map Sum.inr
end LogicLineages.ComputabilityKnowledge.PredictionAttachExit
