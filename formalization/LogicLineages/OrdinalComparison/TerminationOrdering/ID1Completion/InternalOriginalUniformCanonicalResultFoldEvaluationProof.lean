module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
open Source InternalOriginalUniformCanonicalResultFold InternalOriginalUniformCanonicalResultFoldTargets
open InternalParameterizedCanonicalResultFold (Data validity rootGuard leaf combine foldN goodRunH)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalOriginalUniformCanonicalResultFoldSupportProof
open InternalApplicationValidityStack InternalApplicationValidityStackStateProof
open InternalParameterizedApplicationResultFoldCalibration
open InternalParameterizedApplicationResultFoldCalibrationProof
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Strong induction measures the ORIGINAL input payload. Both original
children keep the same parameter, while their computed output sizes remain
unrestricted. Every unopened root uses the all-input original fallback. -/
theorem semanticCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat) :
    semanticFoldP (rootGuard data) (leaf data) (combine data) value
      (parameterCode symbols S Gamma table) =
      targetRepresentativeValue n arity symbols S Gamma value := by
  let parameter := parameterCode symbols S Gamma table
  have hsource (x : Nat)
      (hop : tagValue x = 2 ∧ evaluate (rootGuard data) (List.Vector.ofFn ![x,parameter]) = 1) :
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma x = 1 := by
    have hs := rootGuardSource data x parameter hop.2
    rw [(actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table x).2] at hs
    exact hs
  suffices allPayloads : ∀ bound x : Nat, payloadValue x = bound →
      semanticFoldP (rootGuard data) (leaf data) (combine data) x parameter =
        targetRepresentativeValue n arity symbols S Gamma x by
    exact allPayloads (payloadValue value) value rfl
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro x hbound
    rw [actualOriginalParameterizedSemanticResultFoldEquation]
    by_cases hop : tagValue x = 2 ∧
        evaluate (rootGuard data) (List.Vector.ofFn ![x,parameter]) = 1
    · rw [if_pos hop]
      have hb := applicationPayloadBound x hop.1
      have hf : payloadValue (functionChildValue x) < bound := by
        rw [functionChildPayload]
        omega
      have ha : payloadValue (argumentChildValue x) < bound := by
        rw [argumentChildPayload]
        omega
      rw [ih (payloadValue (functionChildValue x)) hf (functionChildValue x) rfl,
        ih (payloadValue (argumentChildValue x)) ha (argumentChildValue x) rfl]
      exact openedRootCombine n arity data hc symbols S hS Gamma table x hop.1 (hsource x hop)
    · rw [if_neg hop]
      exact leafCalibration n arity data hc symbols S Gamma table hS x

/-- The existing all-input bounded-stack theorem identifies the literal N
with that semantic fold. Its separate whole-state theorem proves H=1 even
when the original representative is zero; neither fact is reflected into
an object-language derivation. -/
theorem actualOriginalUniformCanonicalResultFoldCalibration :
    ActualOriginalUniformCanonicalResultFoldCalibration := by
  intro n arity data hc symbols S Gamma table hS value
  constructor
  · have h := actualOriginalParameterizedBoundedResultFoldCalibration
      (rootGuard data) (leaf data) (combine data) value (parameterCode symbols S Gamma table)
    exact h.2.trans (semanticCalibration n arity data hc symbols S Gamma table hS value)
  · exact actualOriginalParameterizedResultFoldGoodRunCalibration
      (rootGuard data) (leaf data) (combine data) value (parameterCode symbols S Gamma table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
