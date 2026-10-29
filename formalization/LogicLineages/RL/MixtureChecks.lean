module

public import LogicLineages.RL.MixtureProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_actionLikelihoodLaw (S : Alphabet) : Targets.ActionLikelihoodLaw S :=
  MixtureProof.actionLikelihoodLaw S

theorem fixed_behavioralMixtureRule (S : Alphabet) : Targets.BehavioralMixtureRule S :=
  MixtureProof.behavioralMixtureRule S

theorem fixed_mixtureZeroNoRevival (S : Alphabet) : Targets.MixtureZeroNoRevival S :=
  MixtureProof.mixtureZeroNoRevival S

theorem fixed_behavioralMixtureLikelihood (S : Alphabet) : Targets.BehavioralMixtureLikelihood S :=
  MixtureProof.behavioralMixtureLikelihood S

theorem fixed_traceLikelihoodFactorization (S : Alphabet) : Targets.TraceLikelihoodFactorization S :=
  MixtureProof.traceLikelihoodFactorization S

theorem fixed_behavioralMixtureTrace (S : Alphabet) : Targets.BehavioralMixtureTrace S :=
  MixtureProof.behavioralMixtureTrace S

theorem fixed_behavioralMixtureFiniteValue (S : Alphabet) : Targets.BehavioralMixtureFiniteValue S :=
  MixtureProof.behavioralMixtureFiniteValue S

theorem fixed_behavioralMixtureValue (S : Alphabet) : Targets.BehavioralMixtureValue S :=
  MixtureProof.behavioralMixtureValue S

theorem fixed_behavioralMixtureDeterministicEnvironmentValue (S : Alphabet) : Targets.BehavioralMixtureDeterministicEnvironmentValue S :=
  MixtureProof.behavioralMixtureDeterministicEnvironmentValue S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
