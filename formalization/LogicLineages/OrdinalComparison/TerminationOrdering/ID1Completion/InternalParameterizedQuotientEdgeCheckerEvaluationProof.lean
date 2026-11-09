module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerEvaluationProof
open Source NumberedNumericStep NumberedNumericQuotientEdge
open InternalParameterizedQuotientEdgeChecker InternalParameterizedQuotientEdgeCheckerTargets
open InternalOriginalUniformDescentSelection (Data validity selectedTyped)
open InternalParameterizedCanonicalResultFold (foldN)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (sourceRepresentativeValue targetRepresentativeValue)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (exactOneEvaluation zeroEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalQuotientEdgeCheckerEvaluationProof (originalEdgeDecomposition booleanConjunction)
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalOriginalUniformCanonicalResultFoldEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem fieldEvaluation (selector : Program 1) (v : List.Vector Nat 4) :
    evaluate (field selector) v = evaluate selector (v.get 2 ::ᵥ List.Vector.nil) := by
  change evaluate selector (List.Vector.ofFn fun _ : Fin 1 => v.get 2) = _
  rw [vectorOne]

theorem sourceFieldEvaluation (v : List.Vector Nat 4) :
    evaluate (field source) v = ApplicationCertificateLiftEdge.sourceOf (v.get 2) := by
  rw [fieldEvaluation]
  exact (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).1

theorem targetFieldEvaluation (v : List.Vector Nat 4) :
    evaluate (field target) v = ApplicationCertificateLiftEdge.targetOf (v.get 2) := by
  rw [fieldEvaluation]
  exact (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).2.1

theorem stepFieldEvaluation (v : List.Vector Nat 4) :
    evaluate (field step) v = ApplicationCertificateLiftEdge.stepOf (v.get 2) := by
  rw [fieldEvaluation]
  exact (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).2.2

theorem stepAtEvaluation (data : Data) (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (stepAt data oldStep) v =
      evaluate (InternalOriginalUniformStepGuard.stepChecker data oldStep)
        (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf (v.get 2),
          ApplicationCertificateLiftEdge.targetOf (v.get 2),
          ApplicationCertificateLiftEdge.stepOf (v.get 2),v.get 3]) := by
  change evaluate (InternalOriginalUniformStepGuard.stepChecker data oldStep)
    (List.Vector.ofFn fun i : Fin 4 =>
      evaluate ((![field source,field target,field step,.projection 3] : Fin 4 → Program 4) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases (sourceFieldEvaluation v)
    (Fin.cases (targetFieldEvaluation v)
      (Fin.cases (stepFieldEvaluation v) (Fin.cases rfl (fun q => Fin.elim0 q)))) i

theorem representativeAtEvaluation (representative : Program 2) (selector : Program 1)
    (v : List.Vector Nat 4) :
    evaluate (representativeAt representative selector) v =
      evaluate representative (List.Vector.ofFn ![evaluate (field selector) v,v.get 3]) := by
  change evaluate representative (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((![field selector,.projection 3] : Fin 2 → Program 4) i) v) = _
  congr 1

theorem representativeCheckEvaluation (representative : Program 2) (selector : Program 1)
    (endpoint : Fin 4) (v : List.Vector Nat 4) :
    evaluate (representativeCheck representative selector endpoint) v =
      if evaluate (representativeAt representative selector) v = v.get endpoint then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((![representativeAt representative selector,.projection endpoint] : Fin 2 → Program 4) i) v) = _
  rw [vectorTwo]
  exact exactEqualityEvaluation _ _

theorem coreEvaluation (data : Data) (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (coreChecker data oldStep) v =
      if evaluate (stepAt data oldStep) v = 1 ∧
        evaluate (representativeAt (sourceRepresentative data) source) v = v.get 0 ∧
        evaluate (representativeAt (targetRepresentative data) target) v = v.get 1
      then 1 else 0 := by
  rw [coreChecker,actualConjunctionEvaluation,actualConjunctionEvaluation,
    representativeCheckEvaluation,representativeCheckEvaluation]
  by_cases hs : evaluate (stepAt data oldStep) v = 1 <;>
    by_cases hsource : evaluate (representativeAt (sourceRepresentative data) source) v = v.get 0 <;>
    by_cases htarget : evaluate (representativeAt (targetRepresentative data) target) v = v.get 1 <;>
    simp [hs,hsource,htarget]

theorem sourceCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (value : Nat) :
    evaluate (sourceRepresentative data)
      (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      sourceRepresentativeValue n arity symbols S Gamma value := by
  unfold sourceRepresentative
  rw [evalBranch,exactOneEvaluation,
    (actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table value).2,
    zeroEvaluation,
    (actualOriginalUniformCanonicalResultFoldCalibration n arity data hc symbols S Gamma table hS value).1,
    InternalRepresentativeFoldCalibrationProof.sourceFromTarget]
  by_cases hs : sourceValidityValue n arity symbols S Gamma value = 1 <;>
    simp only [hs,ite_true,ite_false,Nat.one_ne_zero]

theorem targetCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (value : Nat) :
    evaluate (targetRepresentative data)
      (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      targetRepresentativeValue n arity symbols S Gamma value :=
  (actualOriginalUniformCanonicalResultFoldCalibration n arity data hc symbols S Gamma table hS value).1

theorem actualOriginalParameterizedQuotientCoreCalibration :
    ActualOriginalParameterizedQuotientCoreCalibration := by
  intro n arity data oldStep hdata hleaf symbols S Gamma table hS v
  have hw := InternalOriginalUniformStepGuardEvaluationProof.actualOriginalUniformCanonicalStepCalibration
    n arity data oldStep hdata hleaf symbols S Gamma table hS
    (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf (v.get 2),
      ApplicationCertificateLiftEdge.targetOf (v.get 2),ApplicationCertificateLiftEdge.stepOf (v.get 2)])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hw
  rw [coreEvaluation,stepAtEvaluation,representativeAtEvaluation,representativeAtEvaluation,
    sourceFieldEvaluation,targetFieldEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [hw,sourceCalibration n arity data hdata symbols S Gamma table hS,
    targetCalibration n arity data hdata symbols S Gamma table hS,
    originalEdgeDecomposition]
  exact booleanConjunction
    (numericStepTest n arity symbols S Gamma table
      (ApplicationCertificateLiftEdge.sourceOf (v.get 2))
      (ApplicationCertificateLiftEdge.targetOf (v.get 2))
      (ApplicationCertificateLiftEdge.stepOf (v.get 2)))
    (sourceRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLiftEdge.sourceOf (v.get 2)) = v.get 0 ∧
      targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLiftEdge.targetOf (v.get 2)) = v.get 1)

theorem sourceTypeEvaluation (v : List.Vector Nat 4) :
    evaluate sourceType v = (Nat.unpair (v.get 0)).1 := by
  unfold sourceType
  rw [leftOfEvaluation]
  rfl

theorem typedAtEvaluation (data : Data) (endpoint : Fin 4) (v : List.Vector Nat 4) :
    evaluate (typedAt data endpoint) v =
      evaluate (selectedTyped data)
        (List.Vector.ofFn ![v.get endpoint,(Nat.unpair (v.get 0)).1,v.get 3]) := by
  change evaluate (selectedTyped data) (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((![.projection endpoint,sourceType,.projection 3] : Fin 3 → Program 4) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl
    (Fin.cases (sourceTypeEvaluation v) (Fin.cases rfl (fun q => Fin.elim0 q))) i

/-- Original accepted edges satisfy both canonical typed guards. An
original rejection stays zero independently of their values. -/
theorem actualOriginalParameterizedTypedQuotientCalibration :
    ActualOriginalParameterizedTypedQuotientCalibration := by
  intro n arity data oldStep hdata hleaf symbols S Gamma table hS v
  have hcore := actualOriginalParameterizedQuotientCoreCalibration
    n arity data oldStep hdata hleaf symbols S Gamma table hS v
  have htyped := actualOriginalUniformTypedCalibration n arity data hdata symbols S Gamma table hS
  rw [checker,actualConjunctionEvaluation,actualConjunctionEvaluation,
    typedAtEvaluation,typedAtEvaluation,hcore]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [htyped,htyped]
  cases hedge : numericEdgeTest n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) with
  | false => simp only [Bool.toNat_false,Nat.zero_ne_one,false_and,ite_false]
  | true =>
    obtain ⟨hx,hy⟩ := InternalQuotientEdgeTypeGuardEvaluationProof.actualOriginalQuotientEdgeTypedEndpoints
      n arity symbols S Gamma table hS (v.get 0) (v.get 1) (v.get 2) hedge
    rw [hx,hy]
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerEvaluationProof
