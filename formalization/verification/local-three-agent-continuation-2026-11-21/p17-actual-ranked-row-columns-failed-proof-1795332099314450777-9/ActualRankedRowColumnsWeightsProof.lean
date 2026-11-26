module
public import LogicLineages.PermittedControl.ActualRankedRowColumnsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedRowColumns
open PreparedProjection ActualZeroClassReplacement ActualWeightedReadNormalization
open SelectedNonlinearImageBounds (NonlinearField)

theorem exactRankedCoefficients : ExactRankedCoefficients := by
  intro r c xs
  let row := rankedRow r c xs
  have countWeight (k : CountKey r) : row.count k = groupedWeights xs (countOperand r k) := rfl
  have valueWeight (k : ValueKey r) (active : NonlinearField k.2) :
      row.value k = groupedWeights xs (valueOperand r k) := by
    simp only [row,rankedRow,Finsupp.filter_apply,if_pos active,Finsupp.comapDomain_apply]
  have linearWeight (k : ValueKey r) (linear : ¬ NonlinearField k.2) : row.value k = 0 := by
    simp only [row,rankedRow,Finsupp.filter_apply,if_neg linear]
  refine ⟨rfl,countWeight,valueWeight,linearWeight,?_,?_⟩
  · intro k
    simp only [Finsupp.mem_support_iff,countWeight]
  · intro k
    by_cases active : NonlinearField k.2
    · simp only [Finsupp.mem_support_iff,valueWeight k active,active,true_and]
    · simp [Finsupp.mem_support_iff,linearWeight k active,active]

end LogicLineages.PermittedControl.ActualRankedRowColumns
