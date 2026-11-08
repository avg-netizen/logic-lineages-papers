module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTypedEdgePresentation InternalTypedEdgePresentationEvaluationProof

theorem actualOriginalMembershipTypedCalibration :
    InternalTypedEdgePresentationTargets.ActualOriginalMembershipTypedCalibration :=
  InternalTypedEdgePresentationEvaluationProof.actualOriginalMembershipTypedCalibration

theorem actualOriginalTypedEdgePresentation :
    InternalTypedEdgePresentationTargets.ActualOriginalTypedEdgePresentation := by
  intro n arity symbols S Gamma table
  obtain ⟨data,hdata⟩ := calibratedDataExists n arity symbols S Gamma table
  refine ⟨data,hdata,presentationCalibration n arity symbols S Gamma table data hdata,?_⟩
  intro hc body sigma tau α x y a certificate s t k
  obtain ⟨d⟩ := InternalTypedEdgePresentationSupportProof.presentation
    (body := body) (Gamma := [premises data sigma tau x y a certificate s t k])
    S data hdata.2.1 hc sigma tau x y a certificate s t k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationProof
