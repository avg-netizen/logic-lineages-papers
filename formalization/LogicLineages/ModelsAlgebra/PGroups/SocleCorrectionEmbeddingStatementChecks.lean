module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionEmbedding
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_kernel_image : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionKernelImage :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_kernel_image

theorem fixed_socle_correction_embedding : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionEmbedding :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_embedding

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
