module
public import LogicLineages.OrdinalComparison.SelectedBinderCodeSemanticProof
public import LogicLineages.OrdinalComparison.SelectedBinderCodePrimitiveProof
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinderCode.Proof

theorem actualPermutedAssignment : Targets.ActualPermutedAssignment := by
  intro Θ left right σ τ t
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated
    (Θ++(left++σ::right)) τ OrdinalSyntax.defaultPolicy t
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (t.rename (permutation Θ left right σ)) =
      some (SourceRenaming.renameVector (permutation Θ left right σ) u) := by
    rw [SourceRenaming.Proof.assignmentNaturality,hu]
    rfl
  refine ⟨u,hu,hr,?_⟩
  rw [exactSourcePermutation,DefaultSourceAssignment.Proof.assignmentCorrect,hr]
  change some (OrdinalSyntax.vectorCode (SourceRenaming.renameVector (permutation Θ left right σ) u)) = _
  exact congrArg some (exactOrdinalVectorPermutation.2 Θ left right σ τ.level u).symm
end LogicLineages.OrdinalComparison.Source.SelectedBinderCode.Proof
