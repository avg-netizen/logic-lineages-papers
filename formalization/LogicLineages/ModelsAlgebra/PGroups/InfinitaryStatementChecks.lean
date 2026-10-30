module

public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.InfinitaryStatementChecks

theorem fixed_qf_truth_agreement : Targets.groupQFTruthAgreement :=
  GroupInfinitary.qf_truth_agreement

theorem fixed_sigma_qf_padding : Targets.groupSigmaQFPadding :=
  GroupInfinitary.sigma_qf_padding

theorem fixed_pi_qf_padding : Targets.groupPiQFPadding :=
  GroupInfinitary.pi_qf_padding

theorem fixed_truth_transfer : Targets.groupInfinitaryTruthTransfer :=
  GroupInfinitary.truth_transfer

end LogicLineages.ModelsAlgebra.PGroups.InfinitaryStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
