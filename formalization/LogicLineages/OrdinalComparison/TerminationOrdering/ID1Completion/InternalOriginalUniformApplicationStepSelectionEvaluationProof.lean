module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionEvaluationProof
open Source InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformApplicationStepSelectionTargets
open InternalOriginalUniformApplicationStepSelectionPrimitiveProof
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open InternalOriginalUniformParameterLeavesCodecProof
open InternalParameterizedApplicationStepChecker (StepCalibratedAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original paired parameter decodes to exactly this context and
Gamma. Source, target and certificate are otherwise unrestricted raw values. -/
theorem leafCalibrationAt (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hc : LeafCalibrated n arity oldStep) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) :
    StepCalibratedAt n arity symbols S Gamma table oldStep (parameterCode symbols S Gamma table) := by
  intro v
  rw [hc]
  obtain ⟨hcontext,hobject⟩ := actualOriginalUniformParameterCodec.1
    n symbols S Gamma table (v.get 0)
  change (match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
        (Nat.unpair (parameterCode symbols S Gamma table)).1,
      parameterObject (v.get 0) (parameterCode symbols S Gamma table) with
    | some ctx, some obj =>
      (NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 obj.1 ctx.2
        obj.2 (v.get 1) (v.get 2)).toNat
    | _, _ => 0) = _
  rw [hcontext,hobject]

/-- Genuine Program existence is chosen once after n/arity, before every
source window and ambient Gamma. All raw-input calibration is retained. -/
theorem actualOriginalUniformStepLeafProgram : ActualOriginalUniformStepLeafProgram := by
  intro n arity
  obtain ⟨oldStep,hc⟩ := Proof.allPrimitiveFunctions 4 _ (leafValuePrimitive n arity)
  refine ⟨oldStep,hc,?_⟩
  intro symbols S Gamma table
  exact leafCalibrationAt n arity oldStep hc symbols S Gamma table

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionEvaluationProof
