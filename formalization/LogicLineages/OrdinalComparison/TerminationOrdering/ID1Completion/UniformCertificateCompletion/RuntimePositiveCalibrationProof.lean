module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.EvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationProof
open Source
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open InternalParameterizedApplicationStepChecker (EndpointCalibratedAt StepCalibratedAt)
open InternalApplicationStepPeelEvaluationSupportProof
open InternalOriginalUniformDescentSelectionEvaluationProof
open DecodedSourceCalibration EvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- The global original leaf equation applies directly to the caller's raw
parameter. Only the actual decoder equations are substituted. -/
theorem actualOriginalDecodedStepLeafCalibration :
    RuntimePositiveCalibrationTargets.ActualOriginalDecodedStepLeafCalibration := by
  intro n arity oldStep hc parameter ctx hctx Gamma ho v
  rw [hc]
  change (match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
        (Nat.unpair parameter).1, parameterObject (v.get 0) parameter with
    | some c, some obj =>
      (NumberedNumericStep.numericStepTest n arity c.1.1 c.1.2 obj.1 c.2
        obj.2 (v.get 1) (v.get 2)).toNat
    | _, _ => 0) = _
  rw [hctx,ho]

/-- The literal seven-factor endpoint needs three independent callback
slices, including the distinct unrestricted-target validator. -/
theorem endpointSlice (data : Data) (p q : Nat)
    (hs : ∀ value : Nat, evaluate (validity data) (ofFn ![value,p]) =
      evaluate (validity data) (ofFn ![value,q]))
    (ht : ∀ value : Nat, evaluate (targetValidity data) (ofFn ![value,p]) =
      evaluate (targetValidity data) (ofFn ![value,q]))
    (hm : ∀ typ : Nat, evaluate data.member (ofFn ![typ,p]) =
      evaluate data.member (ofFn ![typ,q])) (v : List.Vector Nat 5) :
    evaluate (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
        (ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,p]) =
      evaluate (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
        (ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,q]) := by
  simp only [InternalParameterizedStructuralEndpointGuard.selectedEndpoint,
    InternalParameterizedStructuralEndpointGuard.endpoint,conjunctionEvaluation,
    InternalParameterizedStructuralEndpointGuardEvaluationProof.atEvaluation,
    InternalParameterizedStructuralEndpointGuardEvaluationProof.typeGuardEvaluation,
    List.Vector.get_ofFn]
  let tags : Nat := if (Nat.unpair (v.get 2)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
      (Nat.unpair (v.get 3)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
      (Nat.unpair (v.get 4)).1 = v.get 0 then 1 else 0
  change (if evaluate (validity data) (ofFn ![v.get 2,p]) = 1 ∧
      (if evaluate (targetValidity data) (ofFn ![v.get 3,p]) = 1 ∧
        (if evaluate (validity data) (ofFn ![v.get 4,p]) = 1 ∧
          (if tags = 1 ∧ evaluate data.member (ofFn ![v.get 1,p]) = 1
            then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0) = 1
      then 1 else 0) =
    (if evaluate (validity data) (ofFn ![v.get 2,q]) = 1 ∧
      (if evaluate (targetValidity data) (ofFn ![v.get 3,q]) = 1 ∧
        (if evaluate (validity data) (ofFn ![v.get 4,q]) = 1 ∧
          (if tags = 1 ∧ evaluate data.member (ofFn ![v.get 1,q]) = 1
            then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0) = 1
      then 1 else 0)
  simp only [hs,ht,hm]
  by_cases hsource : evaluate (validity data) (ofFn ![v.get 2,q]) = 1 <;>
    by_cases htarget : evaluate (targetValidity data) (ofFn ![v.get 3,q]) = 1 <;>
    by_cases hargument : evaluate (validity data) (ofFn ![v.get 4,q]) = 1 <;>
    by_cases htags : tags = 1 ∧ evaluate data.member (ofFn ![v.get 1,q]) = 1 <;>
    simp [hsource,htarget,hargument,htags]

/-- Transfer only literal native callback values, never a Context-code
identity. The target slice is paid independently by decoded.targetValidity. -/
theorem endpointCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hd : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx) (Gamma : List Ty)
    (hc : DecodedCalibration n arity data parameter ctx Gamma) :
    EndpointCalibratedAt n arity ctx.1.1 ctx.1.2 Gamma
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) parameter := by
  have hp := SourceComputabilityCompletion.BottomRepresentativeEvaluationProof.decodedLeafSlice
    n arity data hd parameter ctx hctx Gamma hc.objectSlice
  have hq := leafSlice n arity data hd ctx.1.1 ctx.1.2 Gamma ctx.2
  have hv := actualOriginalUniformValidityCalibration n arity data hd ctx.1.1 ctx.1.2 Gamma ctx.2
  intro v
  rw [endpointSlice data parameter (parameterCode ctx.1.1 ctx.1.2 Gamma ctx.2)
    (fun value => (hc.sourceValidity value).trans (hv value).2.symm)
    (fun value => (hc.targetValidity value).trans (hv value).1.symm)
    (fun typ => (hp typ).2.2.2.trans (hq typ).2.2.2.symm)]
  exact InternalParameterizedStructuralEndpointGuardEvaluationProof.actualOriginalParameterizedStructuralEndpointCalibration
    n arity data hd ctx.1.1 ctx.1.2 Gamma ctx.2 v

/-- Original raw guards are redundant on accepted original steps in the
closed decoded window. No numeric endpoint is required to decode in advance. -/
theorem guardedStepCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (oldStep : Program 4) (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (Gamma : List Ty) (hS : SubtypeClosed (fun typ => typ ∈ ctx.1.2))
    (hc : DecodedCalibration n arity data parameter ctx Gamma)
    (hs : StepCalibratedAt n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) parameter) :
    StepCalibratedAt n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (stepChecker data oldStep) parameter := by
  intro v
  let w : List.Vector Nat 4 := ofFn ![v.get 0,v.get 1,v.get 2,parameter]
  have hselected := hs v
  change evaluate (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) w = _ at hselected
  change evaluate (stepChecker data oldStep) w = _
  rw [stepChecker,conjunctionEvaluation,conjunctionEvaluation,hselected]
  cases hn : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) with
  | false => simp
  | true =>
    obtain ⟨hsource,htarget,he⟩ := InternalOriginalStepGuardEvaluationProof.originalAcceptanceGuards
      n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (v.get 0) (v.get 1) (v.get 2) hn
    have huniverse := InternalCertifiedSourceGuardSelectionEvaluationProof.originalStepTargetUniverse
      n arity ctx.1.1 ctx.1.2 Gamma ctx.2 hS (v.get 0) (v.get 1) (v.get 2) hn
    have hg : evaluate (rawGuards data) w = 1 := by
      rw [rawGuards,conjunctionEvaluation,conjunctionEvaluation,
        validityAtEvaluation,validityAtEvaluation,sameOuterTypesEvaluation]
      simp only [w,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      rw [hc.sourceValidity,hc.targetValidity,hsource,htarget]
      simp only [he,ite_true,and_self]
    have hvt : evaluate (validityAt (validity data) 1) w =
        InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma (v.get 1) := by
      rw [validityAtEvaluation]
      exact hc.sourceValidity (v.get 1)
    simp only [hg,hvt,huniverse,Bool.toNat_true,ite_true,and_self]

theorem sourceRepresentativeCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hc : DecodedCalibration n arity data parameter ctx Gamma) (value : Nat) :
    evaluate (UniformCertificateCompletion.sourceRepresentative data) (ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.sourceRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value := by
  rw [UniformCertificateCompletion.sourceRepresentative,InternalAcceptanceCalibrationProof.evalBranch,
    InternalApplicationValidityStackEvaluationProof.exactOneEvaluation,
    InternalApplicationValidityStackEvaluationProof.zeroEvaluation,hc.sourceValidity,hc.fold,
    InternalRepresentativeFoldCalibrationProof.sourceFromTarget]
  by_cases hs : InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma value = 1 <;>
    simp only [hs,ite_true,ite_false,Nat.one_ne_zero]

/-- Calibration follows the ACTUAL edgeChecker AST, whose source and target
representatives intentionally have different filters. -/
theorem edgeCalibration (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hc : DecodedCalibration n arity data parameter ctx Gamma)
    (hs : StepCalibratedAt n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (stepChecker data oldStep) parameter) :
    InternalParameterizedPathChecker.EdgeCalibrated n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (edgeChecker data oldStep) parameter := by
  intro x y certificate
  change evaluate (edgeChecker data oldStep) (ofFn ![x,y,certificate,parameter]) = _
  rw [checkerEvaluation,stepAtEvaluation,representativeAtEvaluation,representativeAtEvaluation,
    fieldSourceEvaluation,fieldTargetEvaluation]
  have hstep := hs (ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,
    ApplicationCertificateLiftEdge.targetOf certificate,ApplicationCertificateLiftEdge.stepOf certificate])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] at hstep
  change (if evaluate (stepChecker data oldStep)
        (ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,
          ApplicationCertificateLiftEdge.targetOf certificate,ApplicationCertificateLiftEdge.stepOf certificate,parameter]) = 1 ∧
      evaluate (UniformCertificateCompletion.sourceRepresentative data)
        (ofFn ![ApplicationCertificateLiftEdge.sourceOf certificate,parameter]) = x ∧
      evaluate (targetRepresentative data)
        (ofFn ![ApplicationCertificateLiftEdge.targetOf certificate,parameter]) = y then 1 else 0) = _
  rw [hstep,sourceRepresentativeCalibration n arity data parameter ctx Gamma hc]
  change (if (NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (ApplicationCertificateLiftEdge.sourceOf certificate)
        (ApplicationCertificateLiftEdge.targetOf certificate)
        (ApplicationCertificateLiftEdge.stepOf certificate)).toNat = 1 ∧
      InternalQuotientEdgeChecker.sourceRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma
        (ApplicationCertificateLiftEdge.sourceOf certificate) = x ∧
      evaluate (InternalParameterizedCanonicalResultFold.foldN data)
        (ofFn ![ApplicationCertificateLiftEdge.targetOf certificate,parameter]) = y then 1 else 0) = _
  rw [hc.fold,InternalQuotientEdgeCheckerEvaluationProof.originalEdgeDecomposition]
  cases hb : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (ApplicationCertificateLiftEdge.sourceOf certificate)
      (ApplicationCertificateLiftEdge.targetOf certificate)
      (ApplicationCertificateLiftEdge.stepOf certificate) <;>
    by_cases hsource : InternalQuotientEdgeChecker.sourceRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma
      (ApplicationCertificateLiftEdge.sourceOf certificate) = x <;>
    by_cases htarget : InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma
      (ApplicationCertificateLiftEdge.targetOf certificate) = y <;>
    simp [hb,hsource,htarget]

/-- One decoded Gamma precedes all raw coordinates, and both original
positive guards remain literal. No new global Program is selected. -/
theorem actualOriginalRuntimePositiveCalibration :
    RuntimePositiveCalibrationTargets.ActualOriginalRuntimePositiveCalibration := by
  intro n arity data oldStep bottom measure hd hl hshape parameter ctx hctx hS
  obtain ⟨Gamma,hc⟩ := DecodedSourceCalibrationProof.actualDecodedCompositeCalibration
    n arity data hd parameter ctx hctx hS
  have hend := endpointCalibration n arity data hd parameter ctx hctx Gamma hc
  have hleaf := actualOriginalDecodedStepLeafCalibration n arity oldStep hl parameter ctx hctx Gamma hc.objectSlice
  have hselected : StepCalibratedAt n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) parameter :=
    InternalParameterizedApplicationStepCheckerEvaluationProof.actualParameterizedOriginalCheckerCalibration
      n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep parameter hend hleaf
  have hguarded := guardedStepCalibration n arity data oldStep parameter ctx Gamma hS hc hselected
  have hedge := edgeCalibration n arity data oldStep parameter ctx Gamma hc hguarded
  refine ⟨Gamma,{
    objectSlice := hc.objectSlice
    targetValidity := hc.targetValidity
    endpoint := hend
    leaf := hleaf
    selectedStep := hselected
    guardedStep := hguarded
    sourceRepresentative := sourceRepresentativeCalibration n arity data parameter ctx Gamma hc
    targetRepresentative := hc.fold
    edge := hedge
    positive := ?_ }⟩
  exact PositiveGuardProof.actualOriginalAllInputPositiveGuardCalibration
    n arity bottom measure (edgeChecker data oldStep) hshape ctx.1.1 ctx.1.2 Gamma ctx.2 parameter hS hedge

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationProof
