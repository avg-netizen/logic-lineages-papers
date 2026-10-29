module

public import LogicLineages.RL.AffineProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_affine_trace_law (S : Alphabet) : Targets.AffineTraceLaw S :=
  AffineProof.affineTraceLaw S

theorem fixed_affine_finite_value (S : Alphabet) : Targets.AffineFiniteValue S :=
  AffineProof.affineFiniteValue S

theorem fixed_affine_value (S : Alphabet) : Targets.AffineValue S :=
  AffineProof.affineValue S

theorem fixed_affine_deterministic_environment_value (S : Alphabet) : Targets.AffineDeterministicEnvironmentValue S :=
  AffineProof.affineDeterministicEnvironmentValue S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
