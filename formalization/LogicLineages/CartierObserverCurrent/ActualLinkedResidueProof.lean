module
public import LogicLineages.CartierObserverCurrent.ActualLinkedResidueTargets
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.ActualLinkedResidue
open LogicLineages.OrdinalComparison

theorem completeActualResidue : Targets.CompleteActualResidue.{u} := by
  intro K _ _ v hv
  simpa only [LogicLineages.OrdinalComparison.Targets.ActualLinkedResidueAt, actualLinkedBudget,
    actualLinkedBinaryExponent, actualLinkedHalfExponent, actualLinkedModulus,
    actualLinkedTail, actualLinkedDegree, actualLinkedOffset, actualLinkedCutoff,
    actualBinarySourceDimension] using fullActualSourceResidue K v hv

#audit_namespace LogicLineages.CartierObserverCurrent.ActualLinkedResidue
end LogicLineages.CartierObserverCurrent.ActualLinkedResidue
