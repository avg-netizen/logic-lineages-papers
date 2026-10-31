module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean.StatementChecks

theorem sourceRunsExact : Targets.SourceRunsExact := Proof.sourceRunsExact
theorem sourceLanguageExact : Targets.SourceLanguageExact := Proof.sourceLanguageExact
theorem sourceComplete : Targets.SourceComplete := Proof.sourceComplete
theorem complementRunsExact : Targets.ComplementRunsExact := Proof.complementRunsExact
theorem complementLanguageExact : Targets.ComplementLanguageExact := Proof.complementLanguageExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean
