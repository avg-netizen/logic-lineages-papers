module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberCalibrationTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberCalibrationProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowPositiveFiberPrograms NumberedWindowPositiveFiberCalibrationTargets
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowConcreteCheckers (positive)

private theorem agreeValue (a : Program 1) (q w v : Nat) :
    evaluate (agree a) (q ::ᵥ w ::ᵥ v ::ᵥ nil) =
      if evaluate a (q ::ᵥ nil) = evaluate a (v ::ᵥ nil) then 1 else 0 := by
  simp only [agree,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,atInput,vectorOne]
  exact exactEqualityEvaluation _ _

private theorem sourceAgrees (entries : NumberedWindowCopyAlgorithm.Entries)
    (s : NumberedWindowScalarAlgorithm.Settings) (q w v : Nat)
    (h : positive entries s q w v = true) :
    contextField q = contextField v ∧ resultField q = resultField v := by
  unfold NumberedWindowConcreteCheckers.positive NumberedWindowAddressCheckers.positive
    NumberedWindowPositivePathAlgorithm.addressRS at h
  cases hq : addressView q with
  | none => simp [hq] at h
  | some qa =>
    cases hv : addressView v with
    | none => simp [hq,hv] at h
    | some va =>
      rcases qa with ⟨qc,qt,qk⟩
      rcases va with ⟨vc,vt,vk⟩
      simp only [hq,hv,Bool.and_eq_true,and_assoc] at h
      obtain ⟨hc,ht,_⟩ := h
      have ec : qc = vc := eq_of_beq hc
      have et : qt = vt := eq_of_beq ht
      simp [contextField,resultField,hq,hv,ec,et]

theorem samePositiveChecker : SamePositiveChecker := by
  intro entries s ctx ty r hctx hty hr q w v
  unfold guarded
  rw [actualConjunctionEvaluation _ _ _ _,actualConjunctionEvaluation _ _ _ _,
    agreeValue,agreeValue,hctx,hctx,hty,hty,hr]
  cases h : positive entries s q w v with
  | false => simp
  | true =>
    obtain ⟨hc,ht⟩ := sourceAgrees entries s q w v h
    simp [hc,ht]
end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberCalibrationProof
