module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.StatementChecks

theorem internalEquationsSound : Targets.InternalEquationsSound := Proof.internalEquationsSound
theorem aliasesSound : Targets.AliasesSound := Proof.aliasesSound
theorem theorySoundness : Targets.TheorySoundness := Proof.theorySoundness
theorem checkExact : Targets.CheckExact := Proof.checkExact
theorem fixedCheckerPrimitive : Targets.FixedCheckerPrimitive := Proof.fixedCheckerPrimitive
theorem proofEmbedding : Targets.ProofEmbedding := Proof.proofEmbedding
theorem internalNumeralCertificates : Targets.InternalNumeralCertificates := Proof.internalNumeralCertificates
theorem specificSourceModel : Targets.SpecificSourceModel := Proof.specificSourceModel

end LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.StatementChecks
