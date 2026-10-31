module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive.StatementChecks

theorem enabledListExact : Targets.EnabledListExact := Proof.enabledListExact
theorem reachableHeightExact : Targets.ReachableHeightExact := Proof.reachableHeightExact
theorem saturation : Targets.Saturation := Proof.saturation
theorem runProductiveExact : Targets.RunProductiveExact := Proof.runProductiveExact
theorem acceptingProductiveExact : Targets.AcceptingProductiveExact := Proof.acceptingProductiveExact
theorem sourceDifferenceEmptyExact : Targets.SourceDifferenceEmptyExact := Proof.sourceDifferenceEmptyExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive
