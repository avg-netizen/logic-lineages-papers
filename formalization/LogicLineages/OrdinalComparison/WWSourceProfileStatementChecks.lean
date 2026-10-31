module
public import LogicLineages.OrdinalComparison.WWSourceProfileProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_sourceHeadClosureProfile : Source.Targets.SourceHeadClosureProfile :=
  Source.SourceClasses.sourceHeadClosureProfile

theorem fixed_sourcePartialNoOmega : Source.Targets.SourcePartialNoOmega :=
  Source.SourceClasses.sourcePartialNoOmega

theorem fixed_sourcePartialHeadHeight : Source.Targets.SourcePartialHeadHeight :=
  Source.SourceClasses.sourcePartialHeadHeight

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
