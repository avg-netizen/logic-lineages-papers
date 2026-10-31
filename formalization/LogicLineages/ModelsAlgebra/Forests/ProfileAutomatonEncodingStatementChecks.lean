module
public import LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding.StatementChecks

theorem familyBoundCorrect : Targets.FamilyBoundCorrect := Proof.familyBoundCorrect

theorem encodingIso : Targets.EncodingIso := Proof.encodingIso

theorem finiteGraphRepresentability : Targets.FiniteGraphRepresentability := Proof.finiteGraphRepresentability

theorem machineCorrect : Targets.MachineCorrect := Proof.machineCorrect

theorem rawAvoidanceDownward : Targets.RawAvoidanceDownward := Proof.rawAvoidanceDownward

theorem arbitraryFiniteFamilyRegular : Targets.ArbitraryFiniteFamilyRegular := Proof.arbitraryFiniteFamilyRegular

end LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding
