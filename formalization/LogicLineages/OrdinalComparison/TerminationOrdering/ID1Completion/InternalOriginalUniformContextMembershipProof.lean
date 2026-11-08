module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipProof
open Source InternalOriginalUniformContextMembership InternalOriginalUniformContextMembershipTargets
open InternalOriginalUniformDescentSelection
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalOriginalUniformContextMembershipEvaluationProof
open InternalOriginalUniformContextMembershipInternalProof

/-- The previously proved five descent laws are generic in the actual Data;
none requires its original membership field or external calibration. -/
theorem descentInternalLaws (data : Data) : InternalLaws data := by
  intro body α Delta
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro value parameter
    exact InternalParameterizedApplicationValidityFoldInternalProof.actualOriginalParameterizedValidityFoldSourceImpliesTarget
      body data.oldSource data.oldTarget data.member α Delta value parameter
  · intro value typ parameter
    exact InternalOriginalUniformDescentSelectionInternalProof.actualParameterizedTypedFactorization
      body data.oldRepresentative (validity data) data.member α Delta value typ parameter
  · intro out input typ parameter
    exact InternalOriginalUniformDescentSelectionInternalProof.actualParameterizedRepresentativeInvariant
      body data.oldRepresentative (validity data) α Delta out input typ parameter
  · intro out input typ parameter
    exact InternalOriginalUniformDescentSelectionInternalProof.actualParameterizedTypedOutput
      body data.oldRepresentative (validity data) data.member α Delta out input typ parameter
  · intro arrow d e fp ap fn arg parent parameter
    exact InternalOriginalUniformDescentSelectionApplicationProof.actualParameterizedSourceApplicationClosure
      body data α Delta arrow d e fp ap fn arg parent parameter

/-- The existing exact calibration theorems apply to every globally
calibrated tuple, including the displayed syntactic normalization. -/
theorem descentCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (hS : SubtypeClosed (fun tau => tau ∈ S)) :
    SelectedCalibrated n arity symbols S Gamma table data := by
  constructor
  · intro value
    have hv := actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table value
    exact ⟨hv.1,hv.2,actualOriginalUniformRepresentativeCalibration
      n arity data hc symbols S Gamma table hS value⟩
  · exact actualOriginalUniformTypedCalibration n arity data hc symbols S Gamma table hS

/-- The selected package is normalizeData of one shared original tuple.
Its syntactic membership law and every calibration/internal-law conclusion
precede all window and Gamma choices. -/
theorem actualOriginalUniformNormalizedMembershipSelection :
    ActualOriginalUniformNormalizedMembershipSelection := by
  intro n arity
  obtain ⟨data,hc,_,_⟩ :=
    InternalOriginalUniformDescentSelectionProof.actualOriginalUniformDescentSelection n arity
  have hn := actualOriginalUniformNormalizedMembershipCalibration n arity data hc
  refine ⟨data,hc,hn,descentInternalLaws (normalizeData data),
    InternalParameterizedCanonicalResultFoldProof.internalLaws (normalizeData data),
    actualOriginalUniformMembershipSlice data.member,?_⟩
  intro symbols S Gamma table hS
  exact ⟨descentCalibration n arity (normalizeData data) hn symbols S Gamma table hS,
    InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
      n arity (normalizeData data) hn symbols S Gamma table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipProof
