module

public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs.StatementChecks

theorem fullArithmeticGraphs : Targets.Target := Proof.fullTarget
theorem termImage : Targets.TermImage := fullArithmeticGraphs.1
theorem formulaImage : Targets.FormulaImage := fullArithmeticGraphs.2.1
theorem termTruth : Targets.TermTruth := fullArithmeticGraphs.2.2.1
theorem boundedTruth : Targets.BoundedTruth := fullArithmeticGraphs.2.2.2.1
theorem programTruth : Targets.ProgramTruth := fullArithmeticGraphs.2.2.2.2.1
theorem allPrimitiveGraphs : Targets.AllPrimitiveGraphs := fullArithmeticGraphs.2.2.2.2.2.1
theorem initialCertificates : Targets.InitialCertificates := fullArithmeticGraphs.2.2.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs
