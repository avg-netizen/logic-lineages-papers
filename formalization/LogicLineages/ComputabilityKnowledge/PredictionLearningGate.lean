module

public import LogicLineages.ComputabilityKnowledge.PredictionLearningProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem prediction_learning :
    Comparators.PredictionLearning.Target := PredictionLearningProof.sourceLearning

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
