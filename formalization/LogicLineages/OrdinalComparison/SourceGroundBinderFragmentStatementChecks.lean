module
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentTargets
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment.StatementChecks
theorem exact_renaming : Targets.ExactRenaming := Proof.exactRenaming
theorem primitive_expressions : Targets.PrimitiveExpressions := Proof.primitiveExpressions
theorem literal_eraser_detectors : Targets.LiteralEraserDetectors := Proof.literalEraserDetectors
theorem literal_aggregate : Targets.LiteralAggregate := Proof.literalAggregate
end LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment
