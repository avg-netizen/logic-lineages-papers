module

public import LogicLineages.RL.EnvironmentMixtureProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_perceptHistoryLikelihoodLaw (S : Alphabet) : Targets.PerceptHistoryLikelihoodLaw S :=
  EnvironmentMixtureProof.perceptHistoryLikelihoodLaw S

theorem fixed_environmentMixtureRule (S : Alphabet) : Targets.EnvironmentMixtureRule S :=
  EnvironmentMixtureProof.environmentMixtureRule S

theorem fixed_environmentMixtureZeroNoRevival (S : Alphabet) : Targets.EnvironmentMixtureZeroNoRevival S :=
  EnvironmentMixtureProof.environmentMixtureZeroNoRevival S

theorem fixed_environmentMixturePerceptTrace (S : Alphabet) : Targets.EnvironmentMixturePerceptTrace S :=
  EnvironmentMixtureProof.environmentMixturePerceptTrace S

theorem fixed_environmentMixtureTrace (S : Alphabet) : Targets.EnvironmentMixtureTrace S :=
  EnvironmentMixtureProof.environmentMixtureTrace S

theorem fixed_environmentMixtureFiniteValue (S : Alphabet) : Targets.EnvironmentMixtureFiniteValue S :=
  EnvironmentMixtureProof.environmentMixtureFiniteValue S

theorem fixed_environmentMixtureAdmissible (S : Alphabet) : Targets.EnvironmentMixtureAdmissible S :=
  EnvironmentMixtureProof.environmentMixtureAdmissible S

theorem fixed_environmentMixtureValue (S : Alphabet) : Targets.EnvironmentMixtureValue S :=
  EnvironmentMixtureProof.environmentMixtureValue S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
