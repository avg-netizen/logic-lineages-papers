module
public import LogicLineages.OrdinalComparison.ContextInsertionCodeSemanticProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ContextInsertionCode.Proof

theorem actualInsertedAssignment : Targets.ActualInsertedAssignment := by
  intro Θ Δ Γ τ t
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated (Θ++Γ) τ OrdinalSyntax.defaultPolicy t
  refine ⟨u,hu,?_⟩
  rw [exactSourceInsertion,DefaultSourceAssignment.Proof.assignmentCorrect,
    SourceRenaming.Proof.assignmentNaturality,hu]
  change some (OrdinalSyntax.vectorCode (SourceRenaming.renameVector (insertion Θ Δ Γ) u)) = _
  exact congrArg some (exactOrdinalVector.2 Θ Δ Γ τ.level u).symm
end LogicLineages.OrdinalComparison.Source.ContextInsertionCode.Proof
