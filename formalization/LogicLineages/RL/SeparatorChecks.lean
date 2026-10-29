module

public import LogicLineages.RL.SeparatorProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_scriptHistoryLaw (S : Alphabet) : Targets.ScriptHistoryLaw S :=
  SeparatorProof.scriptHistoryLaw S

theorem fixed_scriptTraceExtensionality (S : Alphabet) : Targets.ScriptTraceExtensionality S :=
  SeparatorProof.scriptTraceExtensionality S

theorem fixed_valueDistinctionDivergence (S : Alphabet) : Targets.ValueDistinctionDivergence S :=
  SeparatorProof.valueDistinctionDivergence S

theorem fixed_scriptedSeparatorOffPathRule (S : Alphabet) : Targets.ScriptedSeparatorOffPathRule S :=
  SeparatorProof.scriptedSeparatorOffPathRule S

theorem fixed_finiteRewardTail (S : Alphabet) : Targets.FiniteRewardTail S :=
  SeparatorProof.finiteRewardTail S

theorem fixed_scriptedSeparatorAdmissible (S : Alphabet) : Targets.ScriptedSeparatorAdmissible S :=
  SeparatorProof.scriptedSeparatorAdmissible S

theorem fixed_scriptedSeparatorDeterministicValue (S : Alphabet) : Targets.ScriptedSeparatorDeterministicValue S :=
  SeparatorProof.scriptedSeparatorDeterministicValue S

theorem fixed_scriptedSeparatorStochasticBounds (S : Alphabet) : Targets.ScriptedSeparatorStochasticBounds S :=
  SeparatorProof.scriptedSeparatorStochasticBounds S

theorem fixed_firstDivergenceSeparator (S : Alphabet) : Targets.FirstDivergenceSeparator S :=
  SeparatorProof.firstDivergenceSeparator S

theorem fixed_twoValueSeparator (S : Alphabet) : Targets.TwoValueSeparator S :=
  SeparatorProof.twoValueSeparator S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
