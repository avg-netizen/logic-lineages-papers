module

public import LogicLineages.ModelsAlgebra.Differential.Hyperplane
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_coordinateRestrictionKernel : Targets.coordinateRestrictionKernel :=
  Hyperplane.restriction_kernel
theorem fixed_coordinateProductMissingWitness : Targets.coordinateProductMissingWitness :=
  Hyperplane.product_missing_witness

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
