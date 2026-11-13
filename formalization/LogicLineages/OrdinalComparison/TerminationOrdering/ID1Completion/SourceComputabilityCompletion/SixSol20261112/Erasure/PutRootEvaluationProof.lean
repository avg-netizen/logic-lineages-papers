module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootWorkingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootEvaluationProof
open PutRoot
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem resultCodeEvaluation (v : List.Vector Nat 2) :
    evaluate resultCode v = resultValue (v.get 0) (v.get 1) := by
  simp only [resultCode,resultValue,pairOfEvaluation,leftOfEvaluation,rightOfEvaluation,
    constantEvaluation,projectionEvaluation]

theorem certificateCodeEvaluation (v : List.Vector Nat 2) :
    evaluate certificateCode v = certificateValue (v.get 0) (v.get 1) := by
  simp only [certificateCode,certificateValue,pairOfEvaluation,constantEvaluation,
    projectionEvaluation,resultCodeEvaluation]

theorem labelOfEvaluation (v : List.Vector Nat 1) :
    evaluate labelOf v = labelValue (v.get 0) := by
  simp only [labelOf,labelValue,rightOfEvaluation,projectionEvaluation]

theorem labelAtEvaluation (v : List.Vector Nat 4) :
    evaluate labelAt v = labelValue (v.get 2) := by
  rw [labelAt,unaryCompositionEvaluation,labelOfEvaluation]
  rfl

theorem resultAtEvaluation (v : List.Vector Nat 4) :
    evaluate resultAt v = resultValue (v.get 0) (labelValue (v.get 2)) := by
  rw [resultAt,binaryCompositionEvaluation,resultCodeEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    projectionEvaluation,labelAtEvaluation]

theorem certificateAtEvaluation (v : List.Vector Nat 4) :
    evaluate certificateAt v = certificateValue (v.get 0) (labelValue (v.get 2)) := by
  rw [certificateAt,binaryCompositionEvaluation,certificateCodeEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    projectionEvaluation,labelAtEvaluation]

theorem activeEvaluation (v : List.Vector Nat 4) :
    evaluate active v = if v.get 2 = certificateValue (v.get 0) (labelValue (v.get 2)) then 1 else 0 := by
  rw [active,sameEvaluation,projectionEvaluation,certificateAtEvaluation]

theorem ordinaryAtEvaluation (v : List.Vector Nat 4) :
    evaluate ordinaryAt v = if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4 then 1 else 0 := by
  simp only [ordinaryAt,sameEvaluation,leftOfEvaluation,rightOfEvaluation,
    projectionEvaluation,constantEvaluation]

theorem acceptedValueEvaluation (source : Program 2) (v : List.Vector Nat 4) :
    evaluate (acceptedValue source) v =
      if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4 ∧
        v.get 1 = resultValue (v.get 0) (labelValue (v.get 2)) then 1 else 0 := by
  rw [acceptedValue,conjunctionEvaluation,conjunctionEvaluation,ordinaryAtEvaluation,
    sameEvaluation,projectionEvaluation,resultAtEvaluation]
  change (if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
    (if (if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4 then 1 else 0) = 1 ∧
      (if v.get 1 = resultValue (v.get 0) (labelValue (v.get 2)) then 1 else 0) = 1
      then 1 else 0) = 1 then 1 else 0) = _
  by_cases hs : evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 <;>
    by_cases ho : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4 <;>
      by_cases ht : v.get 1 = resultValue (v.get 0) (labelValue (v.get 2)) <;> simp [hs,ho,ht]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootEvaluationProof
