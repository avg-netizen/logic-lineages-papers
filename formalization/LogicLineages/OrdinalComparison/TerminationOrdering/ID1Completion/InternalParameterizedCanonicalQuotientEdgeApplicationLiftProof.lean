module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftRuntimeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftProof
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets
open InternalOriginalUniformContextMembership (normalizeData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalParameterizedCanonicalApplicationCalibration :
    ActualOriginalParameterizedCanonicalApplicationCalibration :=
  InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof.actualOriginalParameterizedCanonicalApplicationCalibration

theorem actualParameterizedEncodedCanonicalQuotientEdgeApplicationLift :
    ActualParameterizedEncodedCanonicalQuotientEdgeApplicationLift :=
  InternalParameterizedCanonicalQuotientEdgeApplicationLiftEncodedProof.actualParameterizedEncodedCanonicalQuotientEdgeApplicationLift

theorem actualParameterizedCanonicalQuotientEdgeApplicationLift :
    ActualParameterizedCanonicalQuotientEdgeApplicationLift :=
  InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof.actualParameterizedCanonicalQuotientEdgeApplicationLift

theorem actualParameterizedCanonicalQuotientEdgeApplicationTypedOutputs :
    ActualParameterizedCanonicalQuotientEdgeApplicationTypedOutputs :=
  InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof.actualParameterizedCanonicalQuotientEdgeApplicationTypedOutputs

theorem actualOriginalUniformNormalizedQuotientEdgeApplicationLift :
    ActualOriginalUniformNormalizedQuotientEdgeApplicationLift :=
  InternalParameterizedCanonicalQuotientEdgeApplicationLiftRuntimeProof.actualOriginalUniformNormalizedQuotientEdgeApplicationLift

/-- Both original programs precede every source context. Retain the entire
existing normalized package and attach only conclusions about the same Data. -/
theorem actualOriginalUniformCanonicalQuotientEdgeApplicationSelection :
    ActualOriginalUniformCanonicalQuotientEdgeApplicationSelection := by
  intro n arity
  obtain ⟨data,hbase⟩ :=
    InternalOriginalUniformContextMembershipProof.actualOriginalUniformNormalizedMembershipSelection n arity
  have hc := hbase.1
  have hpackage :=
    (InternalOriginalUniformApplicationTypingProof.actualOriginalUniformNormalizedApplicationTyping
      n arity data hc).1
  have hn := hpackage.1
  obtain ⟨oldStep,hleaf,_⟩ :=
    InternalOriginalUniformApplicationStepSelectionProof.actualOriginalUniformStepLeafProgram n arity
  refine ⟨data,oldStep,hc,hleaf,hpackage,?_,
    actualOriginalUniformNormalizedQuotientEdgeApplicationLift n arity data hc oldStep⟩
  intro symbols S Gamma table hS
  constructor
  · intro x y certificate
    have he := InternalParameterizedQuotientEdgeCheckerEvaluationProof.actualOriginalParameterizedTypedQuotientCalibration
      n arity (normalizeData data) oldStep hn hleaf symbols S Gamma table hS
      (List.Vector.ofFn ![x,y,certificate])
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at he
    change evaluate (InternalParameterizedQuotientEdgeChecker.checker (normalizeData data) oldStep)
      (List.Vector.ofFn ![x,y,certificate,
        InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table]) = _
    rw [he]
    cases NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y certificate <;> rfl
  · exact actualOriginalParameterizedCanonicalApplicationCalibration
      n arity (normalizeData data) hn symbols S Gamma table hS

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftProof
