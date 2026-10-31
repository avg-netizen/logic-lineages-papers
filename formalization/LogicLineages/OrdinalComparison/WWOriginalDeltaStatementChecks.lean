module
public import LogicLineages.OrdinalComparison.WWOriginalDeltaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalHigherCoordinateFree : Source.Targets.OriginalHigherCoordinateFree :=
  Source.OriginalDomain.originalHigherCoordinateFree

theorem fixed_originalDeltaValid : Source.Targets.OriginalDeltaValid :=
  Source.OriginalDomain.originalDeltaValid

theorem fixed_originalSourceAbstractionValid : Source.Targets.OriginalSourceAbstractionValid :=
  Source.OriginalDomain.originalSourceAbstractionValid

theorem fixed_originalDeltaAbstractionComposition : Source.Targets.OriginalDeltaAbstractionComposition :=
  Source.OriginalDomain.originalDeltaAbstractionComposition

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
