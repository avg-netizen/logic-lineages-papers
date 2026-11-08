module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionEvaluationProof
open Source InternalCanonicalQuotientEdgeSelection
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Calibrate the unchanged base application step from exactly the three
original leaves, without assuming any internal closure law. -/
theorem baseCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data) :
    InternalOriginalApplicationStep.SelectedCalibrated n arity symbols S Gamma table
      (baseData data) :=
  InternalOriginalApplicationStepEvaluationProof.selectedCalibration
    n arity symbols S Gamma table (baseData data) ⟨h.1,h.2.1,h.2.2.1⟩

theorem targetSourceValidityEvaluation (data : InternalCanonicalDescentSelection.Data)
    (v : List.Vector Nat 3) :
    evaluate (targetSourceValidityAt data) v =
      evaluate (InternalCanonicalDescentSelection.validity data).sourceValid
        (List.Vector.ofFn ![v.get 1]) := rfl

/-- The extra target SOURCE validity conjunct is redundant on original
accepted steps. Rejected inputs are handled without any decoding assumption. -/
theorem actualOriginalCanonicalEdgeStepCalibration :
    InternalCanonicalQuotientEdgeSelectionTargets.ActualOriginalCanonicalEdgeStepCalibration := by
  intro n arity symbols S Gamma table data hc h v
  have hb := baseCalibration n arity symbols S Gamma table data h
  have hv : evaluate (InternalCanonicalDescentSelection.validity data).sourceValid
      (List.Vector.ofFn ![v.get 1]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 1) :=
    hb.1.1 (List.Vector.ofFn ![v.get 1])
  rw [stepChecker,conjunctionEvaluation,hb.2.2,targetSourceValidityEvaluation,hv]
  cases hn : NumberedNumericStep.numericStepTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2) with
  | false => simp
  | true =>
    have ht := InternalCertifiedSourceGuardSelectionEvaluationProof.originalStepTargetUniverse
      n arity symbols S Gamma table hc (v.get 0) (v.get 1) (v.get 2) hn
    simp [ht]

/-- Only the original step field changes. The original validity, membership,
and both original representative leaf calibrations remain available. -/
theorem selectedLeafCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data) :
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table
      (selectedData data) :=
  ⟨h.1,h.2.1,
    actualOriginalCanonicalEdgeStepCalibration n arity symbols S Gamma table data hc h,
    h.2.2.2⟩

/-- Preserve the full original domains and distinct source/target defaults.
The final component is the all-input equation for the actual numeric edge test. -/
theorem actualOriginalCanonicalEdgeDataCalibration :
    InternalCanonicalQuotientEdgeSelectionTargets.ActualOriginalCanonicalEdgeDataCalibration := by
  intro n arity symbols S Gamma table data hc h
  have hs := actualOriginalCanonicalEdgeStepCalibration n arity symbols S Gamma table data hc h
  have hl := selectedLeafCalibration n arity symbols S Gamma table data hc h
  have hf := InternalCanonicalResultFoldCalibrationProof.actualOriginalCanonicalFoldDataCalibration
    n arity symbols S Gamma table (selectedData data) hc hl
  exact ⟨hs,hf,
    InternalQuotientEdgeCheckerEvaluationProof.actualOriginalCheckerCalibration
      n arity symbols S Gamma table (edgeData data) hf.2.1⟩

/-- The unchanged original finite leaves supply a shared selection before
any internal body, context or symbolic terms are chosen. -/
theorem calibratedDataExists (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    ∃ data : InternalCanonicalDescentSelection.Data,
      InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data :=
  InternalCanonicalDescentSelectionEvaluationProof.calibratedDataExists
    n arity symbols S Gamma table

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionEvaluationProof
