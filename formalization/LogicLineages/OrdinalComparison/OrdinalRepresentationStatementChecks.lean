module
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.CheckedRepresentation

theorem actual_least_fixed_point_calibration : Targets.EpsilonZeroCalibration :=
  epsilonZeroCalibration

theorem all_normal_denotations_below_epsilon_zero : Targets.NormalRepresentationSound :=
  normalRepresentationSound

theorem every_actual_ordinal_below_epsilon_zero_represented :
    Targets.NormalRepresentationComplete := normalRepresentationComplete

end LogicLineages.OrdinalComparison.CheckedRepresentation

#audit_namespace LogicLineages.OrdinalComparison
