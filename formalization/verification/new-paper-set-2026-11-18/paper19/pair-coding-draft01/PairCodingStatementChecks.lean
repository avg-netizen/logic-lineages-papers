module
public import LogicLineages.ControlSensitivityCurrent.PairCodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PairCoding.StatementChecks
theorem fixed_pairCoding : PairCodingTargets.PairCoding := pairCoding
theorem fixed_sortedWitness : PairCodingTargets.SortedWitness := sortedWitness
#audit_namespace LogicLineages.ControlSensitivityCurrent.PairCoding.StatementChecks
end LogicLineages.ControlSensitivityCurrent.PairCoding.StatementChecks
