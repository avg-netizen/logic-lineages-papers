module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
open InternalOriginalUniformContextMembership InternalOriginalUniformContextMembershipTargets
open InternalOriginalUniformParameterLeaves
open InternalOriginalUniformParameterLeavesCodecProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL total Object decoder retains the input type at every raw
parameter. Its decoded Gamma can vary freely because membership ignores it. -/
theorem actualOriginalUniformMembershipParameterIndependence :
    ActualOriginalUniformMembershipParameterIndependence := by
  intro n typ parameter
  obtain ⟨Gamma,hGamma⟩ := actualOriginalUniformParameterCodec.2 typ parameter
  obtain ⟨otherGamma,hOther⟩ := actualOriginalUniformParameterCodec.2 typ
    (Nat.pair (Nat.unpair parameter).1 0)
  simp only [memberValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold decodedValue
  rw [hGamma,hOther]
  simp only [Nat.unpair_pair]
  cases Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1 <;> rfl

theorem contextMemberEvaluation (member : Program 2) (v : List.Vector Nat 2) :
    evaluate (contextMember member) v =
      evaluate member (List.Vector.ofFn ![v.get 0,Nat.pair (v.get 1) 0]) := by
  change evaluate member (List.Vector.ofFn ![v.get 0,
    evaluate (pairOf (.projection 1) (InternalAcceptance.constantZero 2)) v]) = _
  rw [pairOfEvaluation]
  rfl

theorem normalizedMemberEvaluation (member : Program 2) (v : List.Vector Nat 2) :
    evaluate (normalizedMember member) v =
      evaluate member (List.Vector.ofFn ![v.get 0,Nat.pair (Nat.unpair (v.get 1)).1 0]) := by
  change evaluate (contextMember member) (List.Vector.ofFn
    ![v.get 0,evaluate (leftOf (.projection 1)) v]) = _
  rw [contextMemberEvaluation,leftOfEvaluation]
  rfl

/-- All three other ASTs are unchanged; the only new calibration obligation
is the original all-input member identity just proved from the total codec. -/
theorem actualOriginalUniformNormalizedMembershipCalibration :
    ActualOriginalUniformNormalizedMembershipCalibration := by
  intro n arity data hc
  refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
  intro v
  change evaluate (normalizedMember data.member) v = memberValue n v
  rw [normalizedMemberEvaluation,hc.2.2.2]
  have h := actualOriginalUniformMembershipParameterIndependence n (v.get 0) (v.get 1)
  simpa only [memberValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one] using h.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
