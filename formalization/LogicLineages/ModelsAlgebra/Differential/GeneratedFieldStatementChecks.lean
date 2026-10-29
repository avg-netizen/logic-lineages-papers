module

public import LogicLineages.ModelsAlgebra.Differential.GeneratedFieldTargets
public import LogicLineages.ModelsAlgebra.Differential.GeneratedField
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem jetFieldClosed : Targets.jetFieldClosed := by
  intro F _ _ D a
  exact fieldGeneratedByJets_isDerivationClosed D a

theorem jetFieldMinimal : Targets.jetFieldMinimal := by
  intro F _ _ D a E ha hE
  exact fieldGeneratedByJets_le D a E ha hE

theorem jetFieldRestriction : Targets.jetFieldRestriction := by
  intro F _ _ D a
  exact ⟨generatedFieldDerivation D a, fun _ => rfl⟩

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
