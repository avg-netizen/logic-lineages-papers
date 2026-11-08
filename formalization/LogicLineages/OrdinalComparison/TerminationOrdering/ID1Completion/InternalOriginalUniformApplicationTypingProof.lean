module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformApplicationTyping InternalOriginalUniformApplicationTypingTargets
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalOriginalUniformApplicationTypingMembershipProof
open InternalApplicationStepPeelSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem actualOriginalUniformNormalizedMembershipNumeral :
    ActualOriginalUniformNormalizedMembershipNumeral :=
  InternalOriginalUniformApplicationTypingMembershipProof.actualOriginalUniformNormalizedMembershipNumeral

theorem actualOriginalUniformNormalizedCodomainMembership :
    ActualOriginalUniformNormalizedCodomainMembership :=
  InternalOriginalUniformApplicationTypingMembershipProof.actualOriginalUniformNormalizedCodomainMembership

theorem actualParameterizedCanonicalApplicationTypedOutput :
    ActualParameterizedCanonicalApplicationTypedOutput :=
  InternalOriginalUniformApplicationTypingApplicationProof.actualParameterizedCanonicalApplicationTypedOutput

/-- The actual typed function supplies arrow membership at the same runtime
parameter. The closed membership slice and subtype closure supply codomain
membership, so the generic actualJ typing theorem needs no extra premise. -/
theorem runtimeApplicationTyped (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (hS : SubtypeClosed (fun typ => typ ∈ S))
    (sigma tau : Ty) (parameter gammaCode f a out : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Delta
      (runtimePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData data) sigma tau parameter gammaCode f a out))) :
    Nonempty (Derivation body Delta
      (typedGraph (normalizeData data) out (numeral (typeNumber tau)) parameter)) := by
  let normalized := normalizeData data
  have hp := andLeft h
  have hf := andLeft (andRight h)
  have ha := andLeft (andRight (andRight h))
  have hj := andRight (andRight (andRight h))
  have hmArrow := andLeft (InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    normalized.oldRepresentative (InternalOriginalUniformDescentSelection.validity normalized)
    normalized.member f (numeral (typeNumber (.arrow sigma tau))) parameter hf)
  have hm := codomainMembership n arity data hc symbols S table hS sigma tau
    parameter gammaCode hp hmArrow
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral
    (body := body) (Gamma := Delta) (α := α) sigma tau
  exact InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped normalized
    (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
    (numeral (typeNumber tau)) f a out parameter
    (andIntro har (andIntro hm (andIntro hf (andIntro ha hj))))

/-- Strengthen each calibrated base tuple directly. The normalization and
all earlier selected calibrations are retained for the identical Data. -/
theorem actualOriginalUniformNormalizedApplicationTyping :
    ActualOriginalUniformNormalizedApplicationTyping := by
  intro n arity data hc
  have hn := InternalOriginalUniformContextMembershipEvaluationProof.actualOriginalUniformNormalizedMembershipCalibration
    n arity data hc
  constructor
  · refine ⟨hn,
      InternalOriginalUniformContextMembershipProof.descentInternalLaws (normalizeData data),
      InternalParameterizedCanonicalResultFoldProof.internalLaws (normalizeData data),
      InternalOriginalUniformContextMembershipInternalProof.actualOriginalUniformMembershipSlice data.member,?_⟩
    intro symbols S Gamma table hS
    exact ⟨InternalOriginalUniformContextMembershipProof.descentCalibration
        n arity (normalizeData data) hn symbols S Gamma table hS,
      InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
        n arity (normalizeData data) hn symbols S Gamma table hS⟩
  · intro symbols S table hS body α Delta sigma tau parameter gammaCode f a out
    let P := runtimePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (normalizeData data) sigma tau parameter gammaCode f a out
    obtain ⟨h⟩ := runtimeApplicationTyped (body := body) (Delta := P :: Delta)
      n arity data hc symbols S table hS sigma tau parameter gammaCode f a out
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
