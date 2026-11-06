module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPreflight
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsPreflight
def scalarComparator : Prop := JointGammaProgramsTargets.ActualScalarPrimitive
def listComparator : Prop := JointGammaProgramsTargets.ActualListPrimitive
def positiveComparator : Prop := JointGammaProgramsTargets.ActualPositivePrimitive
def directComparator : Prop := JointGammaProgramsTargets.ActualDirectPrimitive
/-- Discharge the existing exact presentation target, not a new weakened presentation. -/
def presentationComparator : Prop := ContextUniformPreflight.presentationComparator
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsPreflight
