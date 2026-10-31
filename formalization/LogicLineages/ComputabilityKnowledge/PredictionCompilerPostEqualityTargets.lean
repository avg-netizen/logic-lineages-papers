module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityTargets
open PredictionCompilerTapeSupport PredictionCompilerPostEquality

def ExactTapeStatementEquality : Prop := ∀ q r : TapeStatement, tapeEq q r = true ↔ q = r

def ExactPostLabelEquality : Prop := ∀ q r : PostLabel, postEq q r = true ↔ q = r

end LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityTargets
