module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesProof
open Source InternalOriginalUniformParameterLeaves
open InternalOriginalUniformParameterLeavesCodecProof InternalOriginalUniformParameterLeavesCalibrationProof
open InternalOriginalUniformParameterLeavesPrimitiveProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalUniformLeafPrograms :
    InternalOriginalUniformParameterLeavesTargets.ActualOriginalUniformLeafPrograms := by
  intro n arity
  obtain ⟨oldSource, hs⟩ := Proof.allPrimitiveFunctions 2 _ (sourcePrimitive n arity)
  obtain ⟨oldTarget, ht⟩ := Proof.allPrimitiveFunctions 2 _ (targetPrimitive n arity)
  obtain ⟨oldRepresentative, hr⟩ := Proof.allPrimitiveFunctions 2 _ (representativePrimitive n arity)
  obtain ⟨member, hm⟩ := Proof.allPrimitiveFunctions 2 _ (memberPrimitive n)
  refine ⟨oldSource,oldTarget,oldRepresentative,member,⟨hs,ht,hr,hm⟩,?_⟩
  intro symbols S Gamma table value
  let v := List.Vector.ofFn ![value,parameterCode symbols S Gamma table]
  have hc := actualOriginalUniformLeafCalibration n arity v
  change evaluate oldSource v = _ ∧ evaluate oldTarget v = _ ∧
    evaluate oldRepresentative v = _ ∧ evaluate member v = _
  rw [hs,ht,hr,hm,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  simp only [v, List.Vector.get_ofFn, Matrix.cons_val_zero, Matrix.cons_val_one,
    decodedValueAtParameter, and_self]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesProof

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesProof
