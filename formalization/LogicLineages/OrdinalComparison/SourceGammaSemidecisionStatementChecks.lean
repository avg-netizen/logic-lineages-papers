module
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionTargets
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.StatementChecks
theorem encoded_witness : Targets.EncodedWitness := Proof.encodedWitness
theorem exact_search : Targets.ExactSearch := Proof.exactSearch
theorem fixed_semidecision : Targets.FixedSemidecision := Proof.fixedSemidecision
theorem universal_normal_form : Targets.UniversalNormalForm := Proof.universalNormalForm
end LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision
