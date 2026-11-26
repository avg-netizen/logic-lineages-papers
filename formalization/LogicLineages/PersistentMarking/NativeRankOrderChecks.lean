import LogicLineages.PersistentMarking.NativeRankOrderTargets
import LogicLineages.PersistentMarking.OrdinalRankSupportProof

namespace LogicLineages.PersistentMarking.NativeRankOrderChecks
open NativeIteratorStrictTargets NativeRankOrderTargets OrdinalRankSupportProof

theorem exact_NativeRankRecurrence : NativeRankRecurrence :=
  fun _ _ _ h => h.rank_eq

theorem exact_NativeRankStrictEdge : NativeRankStrictEdge :=
  fun _ _ _ _ h edge => h.rank_lt_of_rel edge

theorem exact_NativeRankRestriction : NativeRankRestriction :=
  fun _ _ _ h full => exact_RankOfRelationMap Subtype.val (fun h => h) h full

theorem exact_NativeRankSuccessorWitness : NativeRankSuccessorWitness :=
  fun _ _ _ h β bound => exact_RankImmediateSuccessor h β bound

#print axioms exact_NativeRankRecurrence
#print axioms exact_NativeRankStrictEdge
#print axioms exact_NativeRankRestriction
#print axioms exact_NativeRankSuccessorWitness

end LogicLineages.PersistentMarking.NativeRankOrderChecks
