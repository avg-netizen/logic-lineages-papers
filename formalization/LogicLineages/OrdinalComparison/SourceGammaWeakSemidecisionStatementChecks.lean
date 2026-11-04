module
public import LogicLineages.OrdinalComparison.SourceGammaWeakSemidecisionTargets
public import LogicLineages.OrdinalComparison.SourceGammaWeakSemidecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision.StatementChecks
theorem encoded_witness : Targets.EncodedWitness := Proof.encodedWitness
theorem exact_search : Targets.ExactSearch := Proof.exactSearch
theorem fixed_semidecision : Targets.FixedSemidecision := Proof.fixedSemidecision
theorem universal_normal_form : Targets.UniversalNormalForm := Proof.universalNormalForm
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision
