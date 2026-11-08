module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationMeaningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSemanticProof
open Source InternalCanonicalResultFoldCalibration InternalApplicationValidityStack
open InternalApplicationResultFoldCalibration InternalOriginalStepGuard InternalQuotientEdgeChecker
open InternalCanonicalResultFoldCalibrationSupportProof
open InternalCanonicalResultFoldCalibrationApplicationProof
open InternalApplicationValidityStackStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Strong induction ranges over every original packed input at the current
payload. Only original children are recursive arguments; computed output sizes
are unrestricted. The full decision calibration recovers original source
validity, and the NEW raw-application combine uses original congruence. -/
 theorem actualOriginalSemanticCanonicalFoldCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalSemanticCanonicalFoldCalibration := by
  intro n arity symbols S Gamma table data hc h value
  let G : Nat → Nat := fun x => evaluate (rootGuard data) (List.Vector.ofFn ![x])
  let L : Nat → Nat := fun x => evaluate (leaf data) (List.Vector.ofFn ![x])
  let C : Nat → Nat → Nat → Nat → Nat := fun d e f a =>
    evaluate (combine data) (List.Vector.ofFn ![d,e,f,a])
  change semanticFold G L C value = targetRepresentativeValue n arity symbols S Gamma value
  have hv := InternalCanonicalDescentSelectionEvaluationProof.recursiveValidityCalibration
    n arity symbols S Gamma table data h
  have hL (x : Nat) : L x = targetRepresentativeValue n arity symbols S Gamma x :=
    leafCalibration n arity symbols S Gamma table data hc h (List.Vector.ofFn ![x])
  have hG (x : Nat) (hop : tagValue x = 2 ∧ G x = 1) :
      sourceValidityValue n arity symbols S Gamma x = 1 := by
    have he := actualOriginalCanonicalFoldOpeningCalibration
      n arity symbols S Gamma table data hc h (List.Vector.ofFn ![x])
    rw [InternalApplicationResultStackEvaluationProof.openGuardEvaluation,
      InternalApplicationResultStackEvaluationProof.openGuardEvaluation,hv.1] at he
    change (if tagValue x = 2 ∧ G x = 1 then 1 else 0) =
      (if tagValue x = 2 ∧ sourceValidityValue n arity symbols S Gamma x = 1
        then 1 else 0) at he
    rw [if_pos hop] at he
    by_contra hn
    simp only [hn,and_false,ite_false] at he
    exact Nat.one_ne_zero he
  suffices allPayloads : ∀ bound value : Nat, payloadValue value = bound →
      semanticFold G L C value = targetRepresentativeValue n arity symbols S Gamma value by
    exact allPayloads (payloadValue value) value rfl
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro value hbound
    rw [InternalApplicationResultFoldCalibrationMeaningProof.actualOriginalSemanticResultFoldEquation]
    by_cases hop : tagValue value = 2 ∧ G value = 1
    · rw [if_pos hop]
      have hb := applicationPayloadBound value hop.1
      have hf : payloadValue (functionChildValue value) < bound := by
        rw [functionChildPayload]
        omega
      have ha : payloadValue (argumentChildValue value) < bound := by
        rw [argumentChildPayload]
        omega
      rw [ih (payloadValue (functionChildValue value)) hf (functionChildValue value) rfl,
        ih (payloadValue (argumentChildValue value)) ha (argumentChildValue value) rfl]
      exact openedRootCombine n arity symbols S hc Gamma table data h value hop.1 (hG value hop)
    · rw [if_neg hop]
      exact hL value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSemanticProof
