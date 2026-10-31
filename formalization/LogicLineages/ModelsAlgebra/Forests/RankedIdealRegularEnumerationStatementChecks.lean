module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumerationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration.StatementChecks
 theorem pairsComplete : Targets.PairsComplete := Proof.pairsComplete
 theorem setsExact : Targets.SetsExact := Proof.setsExact
 theorem functionsComplete : Targets.FunctionsComplete := Proof.functionsComplete
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration
