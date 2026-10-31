module
public import LogicLineages.OrdinalComparison.WWSourceMacroProfileProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_sourceBoxNoOmega : Source.Targets.SourceBoxNoOmega :=
  Source.SourceClasses.sourceBoxNoOmega

theorem fixed_sourceBoxHeadHeight : Source.Targets.SourceBoxHeadHeight :=
  Source.SourceClasses.sourceBoxHeadHeight

theorem fixed_sourceAbstractionNoOmega : Source.Targets.SourceAbstractionNoOmega :=
  Source.SourceClasses.sourceAbstractionNoOmega

theorem fixed_sourceAbstractionHeadHeight : Source.Targets.SourceAbstractionHeadHeight :=
  Source.SourceClasses.sourceAbstractionHeadHeight

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
