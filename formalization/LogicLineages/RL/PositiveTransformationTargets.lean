module

public import LogicLineages.RL.InteractionDefinitions

/-! Full independent source `prop:positive` for the actual four frameworks.
The two-action premise is local to this existence result, never imposed on
Alphabet or framework. Both nontriviality clauses are inherited from the
unchanged accepted definition of Transformation. No theorem suppliers are
premises. The real sign-case environment map may be noncomputable. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

/-- Every positive cell of the manuscript classification, including both
choices of source and target environment kinds. -/
def PositiveTransformation (S : Alphabet) : Prop :=
  ∀ sourceAgents sourceEnvironments targetAgents targetEnvironments : Kind,
    (∃ a₀ a₁ : S.Action, a₀ ≠ a₁) →
    (sourceAgents = Kind.deterministic ∨ targetAgents = Kind.stochastic) →
    Nonempty (LogicLineages.RL.Transformation
      (framework S sourceAgents sourceEnvironments)
      (framework S targetAgents targetEnvironments))

end LogicLineages.RL.Policy.Targets
