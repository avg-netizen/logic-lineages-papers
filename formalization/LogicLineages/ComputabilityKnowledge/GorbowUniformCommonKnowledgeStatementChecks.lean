module

public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge.StatementChecks

theorem fullCommonKnowledge : Targets.Target := Proof.fullTarget
theorem retainedParameter : Targets.RetainedParameter := fullCommonKnowledge.1
theorem literalBodyRewrite : Targets.LiteralBodyRewrite := fullCommonKnowledge.2.1
theorem numeralBody : Targets.NumeralBody := fullCommonKnowledge.2.2.1
theorem enrichedParameters : Targets.EnrichedParameters := fullCommonKnowledge.2.2.2.1
theorem codeEquation : Targets.CodeEquation := fullCommonKnowledge.2.2.2.2.1
theorem closedFixedPoint : Targets.ClosedFixedPoint := fullCommonKnowledge.2.2.2.2.2.1
theorem concreteCommonKnowledge : Targets.ConcreteCommonKnowledge := fullCommonKnowledge.2.2.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge
