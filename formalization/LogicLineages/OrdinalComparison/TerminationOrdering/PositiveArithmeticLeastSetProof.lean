module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetProof
open PositiveArithmeticOperators PositiveArithmeticTransforms TaggedArithmeticOperators PositiveArithmeticLeastSet
open PositiveArithmeticLeastSetSupportProof

theorem semanticLeastUnfolding : PositiveArithmeticLeastSetTargets.ActualSemanticLeastUnfolding := unfolding

theorem semanticLeastness : PositiveArithmeticLeastSetTargets.ActualSemanticLeastness := leastness

theorem taggedLeastSlices : PositiveArithmeticLeastSetTargets.ActualTaggedLeastSlices := by
  intro scalar multiset context x
  have he : leastSet scalar context ⊆ {y | tagNumber false y ∈ leastSet (combinedOperator scalar multiset) context} := by
    apply leastness
    intro y hy
    apply (unfolding (combinedOperator scalar multiset) context (tagNumber false y)).mpr
    exact (TaggedArithmeticOperatorsProof.taggedBranchIsolation scalar multiset
      (fun z => z∈leastSet (combinedOperator scalar multiset) context) context y).1.mpr hy
  have ho : leastSet multiset context ⊆ {y | tagNumber true y ∈ leastSet (combinedOperator scalar multiset) context} := by
    apply leastness
    intro y hy
    apply (unfolding (combinedOperator scalar multiset) context (tagNumber true y)).mpr
    exact (TaggedArithmeticOperatorsProof.taggedBranchIsolation scalar multiset
      (fun z => z∈leastSet (combinedOperator scalar multiset) context) context y).2.mpr hy
  exact ⟨⟨fun h => (joinEven _ _ x).mp (combinedBelowJoin scalar multiset context h),fun h => he h⟩,
    ⟨fun h => (joinOdd _ _ x).mp (combinedBelowJoin scalar multiset context h),fun h => ho h⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetProof
