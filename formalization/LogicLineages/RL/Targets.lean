module

public import LogicLineages.RL.Definitions

/-! Codex-authored comparator for paper 13, Proposition 7.1
(`prop:noncomposition`). This specifies the full existential statement
before the finite construction is supplied in another module. -/
@[expose] public section

namespace LogicLineages.RL.Targets

def NaturalCompositionFails : Prop :=
  ∃ (F G H : Framework) (first : Transformation F G)
      (second : Transformation G H),
    ¬ AgentsSeparated H (second.agentMap ∘ first.agentMap) ∧
    ¬ EnvironmentVaries H (second.agentMap ∘ first.agentMap)

end LogicLineages.RL.Targets
