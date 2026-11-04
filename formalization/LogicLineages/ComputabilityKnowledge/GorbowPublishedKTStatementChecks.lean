module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedKT.StatementChecks

theorem fullActualKT : Targets.Target := Proof.fullTarget
theorem axiomSoundness : Targets.AxiomSoundness := fullActualKT.1
theorem uniformProofSoundness : Targets.UniformProofSoundness := fullActualKT.2.1
theorem eventualTheorems : Targets.EventualTheorems := fullActualKT.2.2.1
theorem consistency : Targets.Consistency := fullActualKT.2.2.2.1
theorem concretePair : Targets.ConcretePair := fullActualKT.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedKT.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedKT
