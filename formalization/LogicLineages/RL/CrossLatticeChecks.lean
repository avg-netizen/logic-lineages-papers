module

public import LogicLineages.RL.CrossLatticeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_latticeLimit (d : PositiveDenominator) : Targets.LatticeLimit d :=
  CrossLatticeProof.latticeLimit d

theorem fixed_latticeRewardLimit (d : PositiveDenominator) : Targets.LatticeRewardLimit d :=
  CrossLatticeProof.latticeRewardLimit d

theorem fixed_deterministicRewardLattice (F : LogicLineages.RL.Framework) (d : PositiveDenominator) : Targets.DeterministicRewardLattice F d :=
  CrossLatticeProof.deterministicRewardLattice F d

theorem fixed_ddIntegerValue (S : Alphabet) : Targets.DDIntegerValue S :=
  CrossLatticeProof.ddIntegerValue S

theorem fixed_scaledDDCalibration (S : Alphabet) (d : PositiveDenominator) : Targets.ScaledDDCalibration S d :=
  CrossLatticeProof.scaledDDCalibration S d

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
