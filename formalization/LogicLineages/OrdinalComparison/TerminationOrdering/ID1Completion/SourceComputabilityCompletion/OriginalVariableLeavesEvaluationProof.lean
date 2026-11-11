module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesEvaluationProof
open Source NumberedLeastCodeRepresentative NumberedAuxiliaryDecoding
open OriginalVariableLeaves OriginalVariableLeavesCodecProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformParameterLeaves
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] OriginalVariableDecoder.check

theorem variableCheckEvaluation (v : List.Vector Nat 2) :
    evaluate variableCheck v = evaluate OriginalVariableDecoder.check
      (List.Vector.ofFn ![(Nat.unpair (v.get 0)).1,
        (Nat.unpair (Nat.unpair (v.get 0)).2).2,(Nat.unpair (v.get 1)).2]) := by
  change evaluate OriginalVariableDecoder.check (List.Vector.ofFn
    ![evaluate (leftOf (.projection 0)) v,
      evaluate (rightOf (rightOf (.projection 0))) v,
      evaluate (rightOf (.projection 1)) v]) = _
  rw [leftOfEvaluation,rightOfEvaluation,rightOfEvaluation,rightOfEvaluation]
  rfl

theorem variableTagEvaluation (v : List.Vector Nat 2) :
    evaluate variableTag v =
      if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 then 1 else 0 := by
  change evaluate OriginalConstructorLeaf.variableTest
    (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
  simpa only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero] using
    OriginalConstructorLeafEvaluationProof.variableTestEvaluation (v.get 0)

theorem contextCheckEvaluation (n : Nat) (guard : Program 1)
    (hg : ContextGuardCalibrated n guard) (v : List.Vector Nat 2) :
    evaluate (contextCheck guard) v =
      (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
        (Nat.unpair (v.get 1)).1).isSome.toNat := by
  change evaluate guard (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (leftOf (.projection 1)) v) = _
  rw [hg,leftOfEvaluation]
  rfl

theorem typeMemberEvaluation (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (v : List.Vector Nat 2) :
    evaluate (typeMember data.member) v = memberValue n
      (List.Vector.ofFn ![(Nat.unpair (v.get 0)).1,v.get 1]) := by
  change evaluate (InternalOriginalUniformContextMembership.normalizedMember data.member)
    (List.Vector.ofFn ![evaluate (leftOf (.projection 0)) v,v.get 1]) = _
  rw [leftOfEvaluation]
  exact (InternalOriginalUniformContextMembershipEvaluationProof.actualOriginalUniformNormalizedMembershipCalibration
     n arity data hc).2.2.2 _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesEvaluationProof
