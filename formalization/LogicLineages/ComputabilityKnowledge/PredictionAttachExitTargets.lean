module
public import LogicLineages.ComputabilityKnowledge.PredictionAttachExitDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAttachExit.Targets

def BridgeStep : Prop := ∀ (α β : Type) (f : α → Option α) (g : β → Option β)
  (exit : α → β) (a : α), f a = none → step f g exit (.inl a) = some (.inr (exit a))

def RightPhase : Prop := ∀ (α β : Type) (f : α → Option α) (g : β → Option β)
  (exit : α → β) (b : β),
  StateTransition.eval (step f g exit) (.inr b) = Sum.inr <$> StateTransition.eval g b

/-- Equality of partial results preserves divergence in either phase, without
assuming termination, a runtime bound, or a source/validator specification. -/
def FullComposition : Prop := ∀ (α β : Type) (f : α → Option α) (g : β → Option β)
  (exit : α → β) (a : α),
  StateTransition.eval (step f g exit) (.inl a) =
    Sum.inr <$> ((StateTransition.eval f a).bind fun terminal => StateTransition.eval g (exit terminal))
end LogicLineages.ComputabilityKnowledge.PredictionAttachExit.Targets
