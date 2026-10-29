module

public import LogicLineages.RL.InteractionDefinitions

/-! Independent full source `prop:negative` and `thm:classification`, including
the singleton-action qualification. All framework policy spaces, environment
admissibility, and values are the actual previously frozen semantics. Neither
a separator theorem nor a mixture theorem is an added premise. The stronger
cross-environment/lattice proposition is not included in these targets. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

/-- No stochastic-agent to deterministic-agent transformation, for either
source or target environment kind. No distinct-action hypothesis is needed. -/
def NegativeTransformation (S : Alphabet) : Prop :=
  ∀ sourceEnvironments targetEnvironments : Kind,
    ¬ Nonempty (LogicLineages.RL.Transformation
      (framework S Kind.stochastic sourceEnvironments)
      (framework S Kind.deterministic targetEnvironments))

/-- In a singleton action alphabet both actual policy spaces have only one
member, so the first existential nontriviality clause is impossible. -/
def SingletonNoTransformation (S : Alphabet) : Prop :=
  Subsingleton S.Action →
    ∀ sourceAgents sourceEnvironments targetAgents targetEnvironments : Kind,
      ¬ Nonempty (LogicLineages.RL.Transformation
        (framework S sourceAgents sourceEnvironments)
        (framework S targetAgents targetEnvironments))

/-- Full source classification with its action-cardinality qualification.
The accepted Transformation definition includes both nontriviality clauses. -/
def Classification (S : Alphabet) : Prop :=
  ∀ sourceAgents sourceEnvironments targetAgents targetEnvironments : Kind,
    Nonempty (LogicLineages.RL.Transformation
      (framework S sourceAgents sourceEnvironments)
      (framework S targetAgents targetEnvironments)) ↔
      (∃ a₀ a₁ : S.Action, a₀ ≠ a₁) ∧
        (sourceAgents = Kind.deterministic ∨ targetAgents = Kind.stochastic)

end LogicLineages.RL.Policy.Targets
