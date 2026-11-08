module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionProof
open Source InternalOriginalUniformDescentSelection InternalOriginalUniformDescentSelectionTargets
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalOriginalUniformDescentSelectionInternalProof
open InternalOriginalUniformDescentSelectionApplicationProof

/-- The chosen leaves precede every window and ambient context. The exact
same arithmetic ASTs satisfy calibration and every displayed internal law. -/
theorem actualOriginalUniformDescentSelection : ActualOriginalUniformDescentSelection := by
  intro n arity
  obtain ⟨oldSource,oldTarget,oldRepresentative,member,hc,_⟩ :=
    InternalOriginalUniformParameterLeavesProof.actualOriginalUniformLeafPrograms n arity
  let data : Data := ⟨oldSource,oldTarget,oldRepresentative,member⟩
  have hc' : Calibrated n arity data := hc
  refine ⟨data,hc',?_,?_⟩
  · intro body α Delta
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro value parameter
      exact InternalParameterizedApplicationValidityFoldInternalProof.actualOriginalParameterizedValidityFoldSourceImpliesTarget
        body data.oldSource data.oldTarget data.member α Delta value parameter
    · intro value typ parameter
      exact actualParameterizedTypedFactorization
        body data.oldRepresentative (validity data) data.member α Delta value typ parameter
    · intro out input typ parameter
      exact actualParameterizedRepresentativeInvariant
        body data.oldRepresentative (validity data) α Delta out input typ parameter
    · intro out input typ parameter
      exact actualParameterizedTypedOutput
        body data.oldRepresentative (validity data) data.member α Delta out input typ parameter
    · intro arrow d e fp ap fn arg parent parameter
      exact actualParameterizedSourceApplicationClosure body data α Delta
        arrow d e fp ap fn arg parent parameter
  · intro symbols S Gamma table hS
    constructor
    · intro value
      have hv := actualOriginalUniformValidityCalibration n arity data hc' symbols S Gamma table value
      exact ⟨hv.1,hv.2,actualOriginalUniformRepresentativeCalibration
        n arity data hc' symbols S Gamma table hS value⟩
    · exact actualOriginalUniformTypedCalibration n arity data hc' symbols S Gamma table hS

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionProof
