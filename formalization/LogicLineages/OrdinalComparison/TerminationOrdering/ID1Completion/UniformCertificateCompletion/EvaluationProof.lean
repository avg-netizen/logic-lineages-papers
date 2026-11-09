module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.EvaluationProof
open Source
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalUniformParameterLeaves (parameterCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open List.Vector

theorem validityAtEvaluation (P : Program 2) (i : Fin 4) (v : List.Vector Nat 4) :
    evaluate (validityAt P i) v = evaluate P (List.Vector.ofFn ![v.get i,v.get 3]) := by
  change evaluate P (List.Vector.ofFn fun j : Fin 2 => evaluate ((![.projection i,.projection 3] : Fin 2 → Program 4) j) v) = _
  congr 1

theorem sameOuterTypesEvaluation (v : List.Vector Nat 4) :
    evaluate sameOuterTypes v =
      if (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 then 1 else 0 := by
  rw [sameOuterTypes,sameEvaluation,leftOfEvaluation,leftOfEvaluation]
  rfl

theorem stepCalibration (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4)
    (hd : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hl : InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (v : List.Vector Nat 3) :
    evaluate (stepChecker data oldStep)
      (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,parameterCode symbols S Gamma table]) =
      (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat := by
  let p := parameterCode symbols S Gamma table
  let w : List.Vector Nat 4 := List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,p]
  have hc := InternalParameterizedApplicationStepCheckerProof.actualParameterizedOriginalCheckerCalibration
    n arity symbols S Gamma table
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep p
    (InternalParameterizedStructuralEndpointGuardProof.actualOriginalParameterizedStructuralEndpointCalibration
      n arity data hd symbols S Gamma table)
    (InternalOriginalUniformApplicationStepSelectionEvaluationProof.leafCalibrationAt
      n arity oldStep hl symbols S Gamma table) v
  change evaluate (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) w = _ at hc
  have hv (value : Nat) :=
    InternalOriginalUniformDescentSelectionEvaluationProof.actualOriginalUniformValidityCalibration
      n arity data hd symbols S Gamma table value
  change evaluate (stepChecker data oldStep) w = _
  rw [stepChecker,conjunctionEvaluation,conjunctionEvaluation,hc]
  cases hn : NumberedNumericStep.numericStepTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2) with
  | false => simp
  | true =>
    obtain ⟨hs,ht,he⟩ := InternalOriginalStepGuardEvaluationProof.originalAcceptanceGuards
      n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) hn
    have htarget := InternalCertifiedSourceGuardSelectionEvaluationProof.originalStepTargetUniverse
      n arity symbols S Gamma table hS (v.get 0) (v.get 1) (v.get 2) hn
    have hg : evaluate (rawGuards data) w = 1 := by
      rw [rawGuards,conjunctionEvaluation,conjunctionEvaluation,
        validityAtEvaluation,validityAtEvaluation,sameOuterTypesEvaluation]
      simp only [w,p,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      rw [(hv (v.get 0)).2,(hv (v.get 1)).1,hs,ht]
      simp only [he,ite_true,and_self]
    have hvt : evaluate (validityAt (validity data) 1) w =
        InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 1) := by
      rw [validityAtEvaluation]
      simpa only [w,p,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using (hv (v.get 1)).2
    simp only [hg,hvt,htarget,Bool.toNat_true,ite_true,and_self]

theorem sourceRepresentativeCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hd : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat) :
    evaluate (sourceRepresentative data)
      (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.sourceRepresentativeValue n arity symbols S Gamma value := by
  have hv := (InternalOriginalUniformDescentSelectionEvaluationProof.actualOriginalUniformValidityCalibration
    n arity data hd symbols S Gamma table value).2
  have hn := (InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
    n arity data hd symbols S Gamma table hS value).1
  rw [sourceRepresentative,InternalAcceptanceCalibrationProof.evalBranch,
    InternalApplicationValidityStackEvaluationProof.exactOneEvaluation,
    InternalApplicationValidityStackEvaluationProof.zeroEvaluation,hv,hn,
    InternalRepresentativeFoldCalibrationProof.sourceFromTarget]
  by_cases hs : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value = 1 <;>
    simp only [hs,ite_true,ite_false,Nat.one_ne_zero]

theorem fieldEvaluation (selector : Program 1) (v : List.Vector Nat 4) :
    evaluate (field selector) v = evaluate selector (List.Vector.ofFn ![v.get 2]) := by
  change evaluate selector (List.Vector.ofFn fun _ : Fin 1 => v.get 2) = _
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

theorem fieldSourceEvaluation (v : List.Vector Nat 4) :
    evaluate (field source) v = ApplicationCertificateLiftEdge.sourceOf (v.get 2) := by
  rw [fieldEvaluation]
  simpa only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero,List.Vector.get_cons_zero] using
    (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).1

theorem fieldTargetEvaluation (v : List.Vector Nat 4) :
    evaluate (field target) v = ApplicationCertificateLiftEdge.targetOf (v.get 2) := by
  rw [fieldEvaluation]
  simpa only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero,List.Vector.get_cons_zero] using
    (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).2.1

theorem fieldStepEvaluation (v : List.Vector Nat 4) :
    evaluate (field step) v = ApplicationCertificateLiftEdge.stepOf (v.get 2) := by
  rw [fieldEvaluation]
  simpa only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero,List.Vector.get_cons_zero] using
    (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).2.2

theorem stepAtEvaluation (data : Data) (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (stepAt data oldStep) v = evaluate (stepChecker data oldStep) (List.Vector.ofFn
      ![ApplicationCertificateLiftEdge.sourceOf (v.get 2),
        ApplicationCertificateLiftEdge.targetOf (v.get 2),
        ApplicationCertificateLiftEdge.stepOf (v.get 2),v.get 3]) := by
  change evaluate (stepChecker data oldStep) (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((![field source,field target,field step,.projection 3] : Fin 4 → Program 4) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases (fieldSourceEvaluation v)
    (Fin.cases (fieldTargetEvaluation v)
      (Fin.cases (fieldStepEvaluation v) (Fin.cases rfl (fun q => Fin.elim0 q)))) i

theorem representativeAtEvaluation (representative : Program 2) (selector : Program 1)
    (v : List.Vector Nat 4) :
    evaluate (representativeAt representative selector) v =
      evaluate representative (List.Vector.ofFn ![evaluate (field selector) v,v.get 3]) := by
  change evaluate representative (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((![field selector,.projection 3] : Fin 2 → Program 4) i) v) = _
  congr 1

theorem checkerEvaluation (data : Data) (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (edgeChecker data oldStep) v =
      if evaluate (stepAt data oldStep) v = 1 ∧
        evaluate (representativeAt (sourceRepresentative data) source) v = v.get 0 ∧
        evaluate (representativeAt (targetRepresentative data) target) v = v.get 1 then 1 else 0 := by
  rw [edgeChecker,conjunctionEvaluation,conjunctionEvaluation,
    representativeCheck,sameEvaluation,representativeCheck,sameEvaluation]
  simp only [projectionEvaluation]
  by_cases hs : evaluate (stepAt data oldStep) v = 1 <;>
    by_cases hx : evaluate (representativeAt (sourceRepresentative data) source) v = v.get 0 <;>
    by_cases hy : evaluate (representativeAt (targetRepresentative data) target) v = v.get 1 <;>
    simp only [hs,hx,hy,ite_true,ite_false,and_self,and_false,false_and,Nat.zero_ne_one]

theorem actualOriginalUniformQuotientEdgeCalibration :
    Targets.ActualOriginalUniformQuotientEdgeCalibration := by
  intro n arity data oldStep hd hl symbols S Gamma table hS x y certificate
  let p := parameterCode symbols S Gamma table
  let v : List.Vector Nat 4 := List.Vector.ofFn ![x,y,certificate,p]
  change evaluate (edgeChecker data oldStep) v = _
  rw [checkerEvaluation,stepAtEvaluation,representativeAtEvaluation,representativeAtEvaluation,
    fieldSourceEvaluation,fieldTargetEvaluation]
  have hs := stepCalibration n arity data oldStep hd hl symbols S Gamma table hS
    (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,
      ApplicationCertificateLiftEdge.targetOf certificate,ApplicationCertificateLiftEdge.stepOf certificate])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hs
  have hr := sourceRepresentativeCalibration n arity data hd symbols S Gamma table hS
    (ApplicationCertificateLiftEdge.sourceOf certificate)
  have ht := (InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
    n arity data hd symbols S Gamma table hS (ApplicationCertificateLiftEdge.targetOf certificate)).1
  change evaluate (stepChecker data oldStep)
    (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,
      ApplicationCertificateLiftEdge.targetOf certificate,ApplicationCertificateLiftEdge.stepOf certificate,p]) = _ at hs
  change evaluate (sourceRepresentative data)
    (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,p]) = _ at hr
  change evaluate (targetRepresentative data)
    (List.Vector.ofFn ![ApplicationCertificateLiftEdge.targetOf certificate,p]) = _ at ht
  change (if evaluate (stepChecker data oldStep)
        (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,
          ApplicationCertificateLiftEdge.targetOf certificate,ApplicationCertificateLiftEdge.stepOf certificate,p]) = 1 ∧
      evaluate (sourceRepresentative data) (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,p]) = x ∧
      evaluate (targetRepresentative data) (List.Vector.ofFn ![ApplicationCertificateLiftEdge.targetOf certificate,p]) = y
      then 1 else 0) = _
  rw [hs,hr,ht,InternalQuotientEdgeCheckerEvaluationProof.originalEdgeDecomposition]
  exact InternalQuotientEdgeCheckerEvaluationProof.booleanConjunction _ _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.EvaluationProof
