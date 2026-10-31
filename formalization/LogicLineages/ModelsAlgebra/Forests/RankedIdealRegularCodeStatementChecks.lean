module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode.StatementChecks
 theorem atomExact : Targets.AtomExact := Proof.atomExact
 theorem atomIdeal : Targets.AtomIdeal := Proof.atomIdeal
 theorem componentExact : Targets.ComponentExact := Proof.componentExact
 theorem productExact : Targets.ProductExact := Proof.productExact
 theorem linearExact : Targets.LinearExact := Proof.linearExact
 theorem productIdeal : Targets.ProductIdeal := Proof.productIdeal
 theorem linearIdeal : Targets.LinearIdeal := Proof.linearIdeal
 theorem componentIdeal : Targets.ComponentIdeal := Proof.componentIdeal
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode
