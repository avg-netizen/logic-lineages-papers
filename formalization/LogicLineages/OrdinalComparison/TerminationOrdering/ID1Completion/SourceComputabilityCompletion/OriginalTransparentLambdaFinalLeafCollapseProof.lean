module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafCollapseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentLambdaFinalFoldLaws OriginalTransparentLambdaFinalFoldProof
open OriginalTransparentLambdaFinalLeafProof OriginalTransparentLambdaFinalApplicationProof
open OriginalTransparentLambdaValidity OriginalTransparentLambdaFinal OriginalHereditaryValidity
open InternalParameterizedApplicationValidityFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem sourceLeafLaw (body : Positive (Fin 1))
    (data : InternalOriginalUniformDescentSelection.Data) :
    LeafLaw body openingGuardP (leafP (BottomParameter.normalized (sourceValidator data)))
      (sourceValidator data) := by
  intro alpha Gamma out input parameter _ h
  obtain ⟨he⟩ := sourceLeafEquation (body := body) (Gamma := Gamma) data out input parameter
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft he) h⟩

theorem targetLeafLaw (body : Positive (Fin 1))
    (data : InternalOriginalUniformDescentSelection.Data) :
    LeafLaw body openingGuardP (leafP (BottomParameter.normalized (targetValidator data)))
      (targetValidator data) := by
  intro alpha Gamma out input parameter _ h
  obtain ⟨he⟩ := targetLeafEquation (body := body) (Gamma := Gamma) data out input parameter
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft he) h⟩

theorem actualOriginalTransparentFinalTargetCollapse :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalTargetCollapse := by
  intro data representative window body alpha Gamma out raw parameter
  exact allOutputEquation openingGuardP (leafP (BottomParameter.normalized (targetValidator data)))
    (targetValidator data) (combineP (InternalLessThan.constantOne 2))
    (targetLeafLaw body data) (targetApplicationLaw body data) out raw parameter

theorem actualOriginalTransparentFinalUniverseCollapse :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalUniverseCollapse := by
  intro data representative window body alpha Gamma out raw parameter
  exact allOutputEquation openingGuardP (leafP (BottomParameter.normalized (sourceValidator data)))
    (sourceValidator data) (combineP (normalizedData data).member)
    (sourceLeafLaw body data) (sourceApplicationLaw body data) out raw parameter
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafCollapseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafCollapseProof
