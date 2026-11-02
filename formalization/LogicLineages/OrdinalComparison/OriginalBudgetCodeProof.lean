module
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeCountProof
public import LogicLineages.OrdinalComparison.OriginalBudgetCodePrimitiveProof
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Proof

theorem actualOriginalBoxBudget : Targets.ActualOriginalBoxBudget := by
  intro k Γ P C hP
  obtain ⟨u,B,caller,b,hu,hB,hC,hb,hge,hbox,hval⟩ :=
    OriginalSecondBudget.Proof.originalFullBoxBudget k Γ P C hP
  refine ⟨u,B,caller,b,hu,hB,hC,?_,hb,hge,hbox,hval⟩
  unfold budgetCode
  rw [DefaultSourceAssignment.Proof.assignmentCorrect,hu]
  change some (secondCode ((OrdinalSyntax.vectorCode u).getD 0 0)) = some b
  have hget : (OrdinalSyntax.vectorCode u).getD 0 0 = OrdinalSyntax.typedCode (u 0) := by
    simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD]
  rw [hget,secondCode,exactCounts]
  simpa only using congrArg some hb.symm
end LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Proof
