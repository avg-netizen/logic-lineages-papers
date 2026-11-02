module
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeSemanticProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodePrimitiveProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode.Proof

theorem actualClosingAssignment : Targets.ActualClosingAssignment := by
  intro Γ τ t
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  have hs : sourceCode (Γ.map SyntaxCode.typeCode) 0 (SyntaxCode.encodeTerm t) =
      SyntaxCode.encodeTerm (UnaryCarrier.closeGround t) := exactProtectedSource [] Γ τ t
  refine ⟨u,hu,hs,?_,UnaryCarrier.Proof.closeGround_no_ground t⟩
  rw [hs,DefaultSourceAssignment.Proof.assignmentCorrect]
  rw [UnaryCarrier.closeGround,GroundClosing.StatementChecks.assignmentNaturality,hu]
  simp only [Option.map_some]
  exact congrArg some (exactOrdinalVector.2 Γ τ.level u).symm
end LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode.Proof
