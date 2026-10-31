module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion.StatementChecks
 theorem productiveExact : Targets.ProductiveExact := Proof.productiveExact
 theorem runExact : Targets.RunExact := Proof.runExact
 theorem acceptanceExact : Targets.AcceptanceExact := Proof.acceptanceExact
 theorem runProductive : Targets.RunProductive := Proof.runProductive
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion
