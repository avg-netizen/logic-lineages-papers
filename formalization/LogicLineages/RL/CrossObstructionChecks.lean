module

public import LogicLineages.RL.CrossObstructionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_actualFrameworkEnvironmentMixtures (S : Alphabet) : Targets.ActualFrameworkEnvironmentMixtures S :=
  CrossObstructionProof.actualFrameworkEnvironmentMixtures S

theorem fixed_crossOrderObstruction  : Targets.CrossOrderObstruction  :=
  CrossObstructionProof.crossOrderObstruction 

theorem fixed_crossFromDeterministicRewards  : Targets.CrossFromDeterministicRewards  :=
  CrossObstructionProof.crossFromDeterministicRewards 

theorem fixed_actualScaledDDCrossObstruction  : Targets.ActualScaledDDCrossObstruction  :=
  CrossObstructionProof.actualScaledDDCrossObstruction 

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
