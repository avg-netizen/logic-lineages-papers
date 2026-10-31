module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompilerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler.StatementChecks
theorem compilationExact : Targets.CompilationExact := Proof.compilationExact
theorem formulaExact : Targets.FormulaExact := Proof.formulaExact
theorem evaluationExact : Targets.EvaluationExact := Proof.evaluationExact
theorem satisfiabilityExact : Targets.SatisfiabilityExact := Proof.satisfiabilityExact
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler
