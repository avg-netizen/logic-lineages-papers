module

public import LogicLineages.ComputabilityKnowledge.PredictionAntiProgramProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem prediction_anti_program :
    Comparators.PredictionAntiProgram.Target := PredictionAntiProgramProof.uniformAntiProgram

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
