module
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Proof

private theorem leaf_free (i j : Nat) : OrdinalSyntax.headLeafFree (8*Nat.pair i j+3) = decide (i≠0) := by
  have hm : (8*Nat.pair i j+3)%8=3 := by omega
  have hd : (8*Nat.pair i j+3)/8=Nat.pair i j := by omega
  simp [OrdinalSyntax.headLeafFree,hm,hd]

theorem exactCounts : Targets.ExactCounts := by
  intro Γ σ q
  unfold countData OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x <;> simp [OrdinalSyntax.termFold,OrdinalSyntax.componentCode,SourceTypedPorts.variableIndex,
      leaf_free,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs,
      HeadFiniteSurplus.secondCount,OriginalSecondBudget.scalarSecond]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    simp only [OrdinalSyntax.termFold,iha,ihb]
    simp [HeadFiniteSurplus.secondCount,OriginalSecondBudget.scalarSecond,ordinalHeadFree,ordinalHeadOccurs]
  | emul a b iha ihb =>
    simp only [OrdinalSyntax.termFold,iha,ihb]
    simp [HeadFiniteSurplus.secondCount,OriginalSecondBudget.scalarSecond,ordinalHeadFree,ordinalHeadOccurs]
  | collapse a b iha ihb =>
    simp only [OrdinalSyntax.termFold,iha,ihb]
    simp [HeadFiniteSurplus.secondCount,OriginalSecondBudget.scalarSecond,ordinalHeadFree,ordinalHeadOccurs]
end LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Proof
