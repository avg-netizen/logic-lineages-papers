module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpointTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusPreflight
open InternalCalculusTargets
def soundnessComparator : Prop := ActualInternalCalculusSoundness
def standardModelComparator : Prop := ActualStandardLeastModel
def invariantComparator : Prop := ActualInternalInvariantInduction
def naturalComparator : Prop := ActualInternalNaturalInduction
def instanceComparator : Prop := ActualInternalInvariantInstance
def wholeSourceComparator : Prop := SourceEndpointTargets.ActualSourceInternalAccessibility
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusPreflight
