module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepEvaluationProof
open OriginalTransparentVariableStep
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalFixedWindowVertexDispatchEvaluationProof (constantEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne)
open OriginalConstructorLeafEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def bottomValue (source : Nat) : Nat :=
  Nat.pair (Nat.unpair source).1 (Nat.pair 3 (Nat.unpair source).1)
def certificateValue (source : Nat) : Nat :=
  Nat.pair 0 (Nat.pair (bottomValue source) (Nat.pair 3 0))

theorem certificateCodeEvaluation (v : List.Vector Nat 1) :
    evaluate certificateCode v = certificateValue (v.get 0) := by
  rw [certificateCode,pairOfEvaluation,pairOfEvaluation,pairOfEvaluation]
  simp only [constantEvaluation]
  change Nat.pair 0 (Nat.pair
    (evaluate BottomRepresentative.bottomCode
      (List.Vector.ofFn fun _ : Fin 1 => evaluate InternalUnpair.left v)) (Nat.pair 3 0)) = _
  rw [leftEvaluation v]
  rw [vectorOne]
  have hb := BottomRepresentativeEvaluationProof.bottomCodeEvaluation (Nat.unpair (v.get 0)).1
  rw [vectorOne] at hb
  change evaluate BottomRepresentative.bottomCode
    ((Nat.unpair (v.get 0)).1 ::ᵥ List.Vector.nil) = _ at hb
  rw [hb]
  rfl

theorem activeEvaluation (v : List.Vector Nat 4) :
    evaluate active v =
      if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 ∧
        v.get 2 = certificateValue (v.get 0) then 1 else 0 := by
  rw [active,conjunctionEvaluation,variableAtEvaluation,sameEvaluation]
  change (if (if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 then 1 else 0) = 1 ∧
    (if v.get 2 = evaluate certificateCode (List.Vector.ofFn fun _ : Fin 1 => v.get 0)
      then 1 else 0) = 1 then 1 else 0) = _
  simp only [certificateCodeEvaluation,List.Vector.get_ofFn]
  split_ifs <;> simp_all

theorem acceptedValueEvaluation (source : Program 2) (v : List.Vector Nat 4) :
    evaluate (acceptedValue source) v =
      if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        v.get 1 = bottomValue (v.get 0) then 1 else 0 := by
  rw [acceptedValue,conjunctionEvaluation,sameEvaluation,expectedBottomEvaluation]
  change (if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
    (if v.get 1 = bottomValue (v.get 0) then 1 else 0) = 1 then 1 else 0) = _
  split_ifs <;> simp_all
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepEvaluationProof
