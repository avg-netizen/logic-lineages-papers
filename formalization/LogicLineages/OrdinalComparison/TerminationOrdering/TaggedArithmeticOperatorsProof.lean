module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsProof
open PositiveArithmeticOperators PositiveArithmeticTransforms TaggedArithmeticOperators
open PositiveArithmeticOperatorsSupportProof TaggedArithmeticOperatorsSupportProof

theorem tagPartition : TaggedArithmeticOperatorsTargets.ActualTagPartition := by
  intro z
  have hm := Nat.mod_lt z (by omega : 0<2)
  have hd := Nat.mod_add_div z 2
  by_cases he : z%2=0
  · refine ⟨(false,z/2),?_,?_⟩
    · simp [tagNumber]; omega
    · rintro ⟨b,x⟩ hx
      cases b <;> simp [tagNumber] at hx
      · have hx' : x=z/2 := by omega
        simp [hx']
      · omega
  · refine ⟨(true,z/2),?_,?_⟩
    · simp [tagNumber]; omega
    · rintro ⟨b,x⟩ hx
      cases b <;> simp [tagNumber] at hx
      · omega
      · have hx' : x=z/2 := by omega
        simp [hx']

theorem taggedBranchIsolation : TaggedArithmeticOperatorsTargets.ActualTaggedBranchIsolation := by
  intro scalar multiset P context x
  constructor
  · rw [combinedOperator,conjTruth,sameBranch,branchTruth]
    constructor
    · exact And.left
    · intro h
      exact ⟨h,fun y he => False.elim (tagsDisjoint x y he)⟩
  · rw [combinedOperator,conjTruth,branchTruth,sameBranch]
    constructor
    · exact And.right
    · intro h
      exact ⟨fun y he => False.elim (tagsDisjoint y x he.symm),h⟩

theorem combinedMonotonicity : TaggedArithmeticOperatorsTargets.ActualCombinedMonotonicity := by
  intro scalar multiset P Q h context z
  exact PositiveArithmeticOperatorsProof.positiveMonotonicity _ (combinedOperator scalar multiset) P Q h _

theorem taggedSourceOperators : TaggedArithmeticOperatorsTargets.ActualTaggedSourceOperators := by
  intro n arity Gamma
  obtain ⟨scalar,multiset,h⟩ := PositiveArithmeticOperatorsProof.sourcePositiveOperators n arity Gamma
  refine ⟨combinedOperator scalar multiset,?_⟩
  intro P context x
  exact ⟨((taggedBranchIsolation scalar multiset P context x).1).trans ((h (fun y => P (tagNumber false y)) context x).1),
    ((taggedBranchIsolation scalar multiset P context x).2).trans ((h (fun y => P (tagNumber true y)) context x).2)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsProof
