module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardEvaluationProof
open Source NumberedNumericStep InternalOriginalUniformStepGuard
open InternalOriginalUniformStepGuardTargets
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem atParameterEvaluation (P : Program 2) (i : Fin 4) (v : List.Vector Nat 4) :
    evaluate (atParameter P i) v = evaluate P (List.Vector.ofFn ![v.get i,v.get 3]) := rfl

theorem sameOuterTypesEvaluation (v : List.Vector Nat 4) :
    evaluate sameOuterTypes v =
      if (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 then 1 else 0 := by
  rw [sameOuterTypes,sameEvaluation,leftOfEvaluation,leftOfEvaluation]
  rfl

/-- The given oldStep is calibrated globally. No new leaf is selected when
the original window and Gamma are supplied. -/
theorem coreCalibration (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hl : InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    InternalParameterizedApplicationStepChecker.StepCalibratedAt n arity symbols S Gamma table
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)
      (parameterCode symbols S Gamma table) :=
  InternalParameterizedApplicationStepCheckerProof.actualParameterizedOriginalCheckerCalibration
    n arity symbols S Gamma table
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep
    (parameterCode symbols S Gamma table)
    (InternalParameterizedStructuralEndpointGuardProof.actualOriginalParameterizedStructuralEndpointCalibration
      n arity data hc symbols S Gamma table)
    (InternalOriginalUniformApplicationStepSelectionEvaluationProof.leafCalibrationAt
      n arity oldStep hl symbols S Gamma table)

/-- Original accepted steps supply all three outer guards. Every rejected
or malformed input is covered by the rejected core conjunct. -/
theorem actualOriginalUniformGuardedStepCalibration :
    ActualOriginalUniformGuardedStepCalibration := by
  intro n arity data oldStep hc hl symbols S Gamma table v
  let parameter := parameterCode symbols S Gamma table
  let vv : List.Vector Nat 4 := List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,parameter]
  have hcStep := coreCalibration n arity data oldStep hc hl symbols S Gamma table v
  have hs := InternalOriginalUniformDescentSelectionEvaluationProof.actualOriginalUniformValidityCalibration
    n arity data hc symbols S Gamma table (v.get 0)
  have ht := InternalOriginalUniformDescentSelectionEvaluationProof.actualOriginalUniformValidityCalibration
    n arity data hc symbols S Gamma table (v.get 1)
  change evaluate (guardedStep data oldStep) vv = _
  rw [guardedStep,guardedChecker,conjunctionEvaluation,hcStep]
  cases hn : numericStepTest n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) with
  | false => simp only [Bool.toNat_false,Nat.zero_ne_one,and_false,ite_false]
  | true =>
    obtain ⟨hsource,htarget,he⟩ := InternalOriginalStepGuardEvaluationProof.originalAcceptanceGuards
      n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) hn
    have hg : evaluate (guards (validity data) (targetValidity data)) vv = 1 := by
      rw [guards,conjunctionEvaluation,conjunctionEvaluation,
        atParameterEvaluation,atParameterEvaluation,sameOuterTypesEvaluation]
      change (if evaluate (validity data) (List.Vector.ofFn ![v.get 0,parameter]) = 1 ∧
        (if evaluate (targetValidity data) (List.Vector.ofFn ![v.get 1,parameter]) = 1 ∧
          (if (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 then 1 else 0) = 1
          then 1 else 0) = 1 then 1 else 0) = 1
      simp only [parameter,hs.2,ht.1,hsource,htarget,he,ite_true,and_self]
    simp only [hg,Bool.toNat_true,and_self,ite_true]

/-- Subtype closure is needed only to make the original target-universe
conjunct redundant. The equality still quantifies over every raw triple. -/
theorem actualOriginalUniformCanonicalStepCalibration :
    ActualOriginalUniformCanonicalStepCalibration := by
  intro n arity data oldStep hc hl symbols S Gamma table hS v
  let parameter := parameterCode symbols S Gamma table
  let vv : List.Vector Nat 4 := List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,parameter]
  have hb := actualOriginalUniformGuardedStepCalibration
    n arity data oldStep hc hl symbols S Gamma table v
  have ht := (InternalOriginalUniformDescentSelectionEvaluationProof.actualOriginalUniformValidityCalibration
    n arity data hc symbols S Gamma table (v.get 1)).2
  have hv : evaluate (targetSourceValidityAt data) vv =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 1) := by
    change evaluate (validity data) (List.Vector.ofFn ![v.get 1,parameter]) = _
    exact ht
  change evaluate (stepChecker data oldStep) vv = _
  rw [stepChecker,conjunctionEvaluation,hb,hv]
  cases hn : numericStepTest n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) with
  | false => simp
  | true =>
    have htarget := InternalCertifiedSourceGuardSelectionEvaluationProof.originalStepTargetUniverse
      n arity symbols S Gamma table hS (v.get 0) (v.get 1) (v.get 2) hn
    simp [htarget]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardEvaluationProof
