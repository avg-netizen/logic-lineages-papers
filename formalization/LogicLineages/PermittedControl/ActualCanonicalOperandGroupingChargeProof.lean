module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
open ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualReadChargeIteration

private theorem weightsOfPerm (out old : List Read) (same : out.Perm old) :
    groupedWeights out = groupedWeights old := by
  induction same with
  | nil => rfl
  | cons rd _ ih =>
      simp only [groupedWeights,ih]
  | swap a b rest =>
      simp only [groupedWeights]
      exact add_left_comm _ _ _
  | trans left right ihLeft ihRight => exact ihLeft.trans ihRight

theorem exactCanonicalCharge : ExactCanonicalCharge := by
  intro r c out old same
  have weights := weightsOfPerm out old same
  refine ⟨weights,?_⟩
  simp only [stateCharge,rankedRow,weights]

end LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
