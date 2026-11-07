module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecPreflight
open InternalListCodecTargets InternalListCodecEvaluationTargets
def comparator0 : Prop := ActualOriginalConsIntroduction
def comparator1 : Prop := ActualOriginalConsDestruction
def comparator2 : Prop := ActualOriginalConsDestructorEquations
def comparator3 : Prop := ActualOriginalConsInjectivity
def comparator4 : Prop := ActualOriginalNilTestGraph
def comparator5 : Prop := ActualOriginalListCodecTotalFunctional
def comparator6 : Prop := ExactListCodecEvaluation
def comparator7 : Prop := ExactSourceListEncoding
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecPreflight
