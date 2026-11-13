module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutPreparationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCalibrationProof
open Source InternalOriginalUniformParameterLeaves
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof
open OriginalActiveClassKernelEvaluationProof
open EvaluatorKeyPut

theorem classEvaluation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) (v : List.Vector Nat 3) :
 evaluate (classTest p H G W P) v =
 if evaluate (OriginalActiveObservedClass.activation (prepared p H G W) H G W) (ofFn ![v.get 0,v.get 2]) = 0
 then evaluate P v else evaluate (kernel p H G W) v := by
 rw [classTest,evalBranch,seedQueryEvaluation]

theorem kernelEvaluation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (v : List.Vector Nat 3) :
 evaluate (kernel p H G W) v =
 if evaluate (OriginalTypedDecoder.target H G) (ofFn ![v.get 1,v.get 2]) = 1 ∧
    evaluate (OriginalActiveObservedClass.activation (prepared p H G W) H G W) (ofFn ![v.get 1,v.get 2]) = 1 ∧
    evaluate (evaluatorKey p H G W) (ofFn ![v.get 0,v.get 2]) =
    evaluate (evaluatorKey p H G W) (ofFn ![v.get 1,v.get 2]) then 1 else 0 := by
 rw [kernel,conjunctionEvaluation,candidateQueryEvaluation,keyEvaluation,
   OriginalActiveClassKernel.domainProgram,conjunctionEvaluation]
 simp [and_assoc]

theorem calibrated (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3)
 (hp : GlobalSourcePackage.InputsCalibrated n arity p)
 (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
 (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
 (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W)
 (hP : OriginalTransparentMinimum.ClassTestCalibrated n arity P) :
 OriginalTransparentMinimum.ClassTestCalibrated n arity (classTest p H G W P) := by
 intro v
 let q := prepared p H G W
 have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
   (SixSol20261113.Erasure.PutPreparationProof.actualPutPreparation n arity p H G W P hp hH hG hW hP).1
 have hold := OriginalActiveClassKernelCalibrationProof.actualOriginalActiveClassKernelCalibration
   n arity q H G W P hq hH hG hW hP v
 rw [OriginalActiveClassKernelEvaluationProof.classEvaluation] at hold
 rw [classEvaluation]
 by_cases hz : evaluate (OriginalActiveObservedClass.activation q H G W) (ofFn ![v.get 0,v.get 2]) = 0
 · simpa only [hz,ite_true] using hold
 · simp only [hz,ite_false] at hold ⊢
   rw [← hold, kernelEvaluation,OriginalActiveClassKernelEvaluationProof.kernelEvaluation]
   have ha := (activationAcceptance q H G W (v.get 0) (v.get 2)).mp
     (activationNonzero q H G W (v.get 0) (v.get 2) hz)
   by_cases hc : evaluate (OriginalTypedDecoder.target H G) (ofFn ![v.get 1,v.get 2]) = 1 ∧
       evaluate (OriginalActiveObservedClass.activation q H G W) (ofFn ![v.get 1,v.get 2]) = 1
   · have hca := (activationAcceptance q H G W (v.get 1) (v.get 2)).mp hc.2
     have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 = 1 := by
       have hw : evaluate q.window (ofFn ![(Nat.unpair (v.get 2)).1]) = 1 := by
         simpa only [BottomRepresentativeEvaluationProof.windowAtEvaluation] using ha.1
       have hwcal := hq.2.1 (ofFn ![(Nat.unpair (v.get 2)).1])
       change evaluate q.window (ofFn ![(Nat.unpair (v.get 2)).1]) = GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 at hwcal
       exact hwcal.symm.trans hw
     obtain ⟨ctx,hctx,hclosed⟩ := (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 2)).1).1.mp hwindow
     obtain ⟨Gamma,hgamma⟩ := OriginalTransparentLambdaValidityParameterProof.parameterGamma (v.get 2)
     let t := OriginalTransparentDecoderSelection.transparentInputs H G W q
     have ht : GlobalSourcePackage.InputsCalibrated n arity t :=
       (OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration n arity q H G W hq hH hG hW).1
     have hs := BottomRepresentativeEvaluationProof.decodedLeafSlice n arity t.base ht.1 (v.get 2) ctx hctx Gamma
       (fun value => OriginalTransparentLambdaValidityParameterProof.objectAtGamma value (v.get 2) Gamma hgamma) (v.get 0)
     have hr := BottomRepresentativeEvaluationProof.decodedLeafSlice n arity t.base ht.1 (v.get 2) ctx hctx Gamma
       (fun value => OriginalTransparentLambdaValidityParameterProof.objectAtGamma value (v.get 2) Gamma hgamma) (v.get 1)
     have he := EvaluatorKeyRawProof.rawKeyIff n arity q.base hq.1 (v.get 2) (v.get 0) (v.get 1) ctx Gamma hctx hclosed hgamma
       (hs.1.symm.trans ha.2) (hr.1.symm.trans hca.2)
     change ((evaluate (evaluatorKey p H G W) (ofFn ![v.get 0,v.get 2]) =
       evaluate (evaluatorKey p H G W) (ofFn ![v.get 1,v.get 2])) ↔ _) at he
     simp only [hc.1,hc.2,true_and,he]
   · have hno : ¬ (evaluate (OriginalTypedDecoder.target H G) (ofFn ![v.get 1,v.get 2]) = 1 ∧
       evaluate (OriginalActiveObservedClass.activation q H G W) (ofFn ![v.get 1,v.get 2]) = 1) := hc
     by_cases ht : evaluate (OriginalTypedDecoder.target H G) (ofFn ![v.get 1,v.get 2]) = 1
     · have ha0 : evaluate (OriginalActiveObservedClass.activation q H G W) (ofFn ![v.get 1,v.get 2]) ≠ 1 := fun ha1 => hno ⟨ht,ha1⟩
       simp only [ht,ha0,false_and,true_and,ite_false]
     · simp only [ht,false_and,ite_false]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCalibrationProof
