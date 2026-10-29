module

public import LogicLineages.RL.PolicySemanticsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_history_correspondence (S : Alphabet) : Targets.HistoryCorrespondence S :=
  PolicySemanticsProof.historyCorrespondence S

theorem fixed_trace_correspondence (S : Alphabet) : Targets.TraceCorrespondence S :=
  PolicySemanticsProof.traceCorrespondence S

theorem fixed_finite_trace_law (S : Alphabet) : Targets.FiniteTraceLaw S :=
  PolicySemanticsProof.finiteTraceLaw S

theorem fixed_deterministic_calibration (S : Alphabet) : Targets.DeterministicCalibration S :=
  PolicySemanticsProof.deterministicCalibration S

theorem fixed_initial_horizon_calibration (S : Alphabet) : Targets.InitialHorizonCalibration S :=
  PolicySemanticsProof.initialHorizonCalibration S

theorem fixed_value_limit (S : Alphabet) : Targets.ValueLimit S :=
  PolicySemanticsProof.valueLimit S

theorem fixed_first_action_policy (S : Alphabet) : Targets.FirstActionPolicy S :=
  PolicySemanticsProof.firstActionPolicy S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
