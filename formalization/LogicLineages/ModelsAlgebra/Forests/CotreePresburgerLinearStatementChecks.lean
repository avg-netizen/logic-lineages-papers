module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinearProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear.StatementChecks

theorem termTranslationExact : Targets.TermTranslationExact := Proof.termTranslationExact
theorem lastVariableSplitExact : Targets.LastVariableSplitExact := Proof.lastVariableSplitExact
theorem substitutionExact : Targets.SubstitutionExact := Proof.substitutionExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear
