module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainPreflight
def codecComparator : Prop := JointGammaDomainTargets.ActualObjectCodec
def primitiveComparator : Prop := JointGammaDomainTargets.ActualGuardPrimitive
def calibrationComparator : Prop := JointGammaDomainTargets.ActualGuardCalibration
def domainComparator : Prop := JointGammaDomainTargets.ActualArgumentDomain
def quantifierComparator : Prop := JointGammaDomainTargets.ActualQuantifierFibers
def typedComparator : Prop := JointGammaDomainTargets.ActualTypedArgumentFibers
def formulaComparator : Prop := JointGammaDomainTargets.ActualGuardArithmeticFormula
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainPreflight
