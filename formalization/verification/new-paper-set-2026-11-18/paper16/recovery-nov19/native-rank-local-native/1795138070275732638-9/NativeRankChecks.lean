import LogicLineages.PersistentMarking.NativeRankGlobalTargets
import LogicLineages.PersistentMarking.NativeRankCountabilityProof

namespace LogicLineages.PersistentMarking.NativeRankChecks
open NativeIteratorStrictTargets NativeSyntaxCountabilityTargets NativeRankTargets NativeRankGlobalTargets

theorem exact_NativeRankRecurrence : NativeRankRecurrence :=
  NativeRankOrderProof.recurrence

theorem exact_NativeRankStrictEdge : NativeRankStrictEdge :=
  NativeRankOrderProof.edgeDrop

theorem exact_NativeRankRestriction : NativeRankRestriction :=
  NativeRankOrderProof.restriction

theorem exact_NativeRankSuccessorWitness : NativeRankSuccessorWitness :=
  NativeRankOrderProof.successorWitness

theorem exact_CountableNativeRanks : CountableNativeRanks :=
  NativeRankCountabilityProof.countableRanks

theorem compose (nativeWF : ClosedNativeStrictWellFounded)
    (confinedWF : ∀ S, WellFounded (fun t s : Spine.Expr => ConfinedPair.Strict S s t))
    (codes : ClosedNativeCountability) : ActualClosedNativeRanks := by
  intro S τ
  refine ⟨nativeWF S τ, confinedWF S, fun s => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact exact_CountableNativeRanks codes S τ s (nativeWF S τ |>.apply s)
  · exact exact_NativeRankRestriction S τ s (nativeWF S τ |>.apply s)
      (confinedWF S |>.apply s.val)
  · exact exact_NativeRankRecurrence S τ s (nativeWF S τ |>.apply s)
  · intro t edge
    exact exact_NativeRankStrictEdge S τ s t (nativeWF S τ |>.apply s) edge
  · intro β bound
    obtain ⟨t, edge, ht⟩ :=
      exact_NativeRankSuccessorWitness S τ s (nativeWF S τ |>.apply s) β bound
    exact ⟨t, edge, ht⟩

#print axioms exact_NativeRankRecurrence
#print axioms exact_NativeRankStrictEdge
#print axioms exact_NativeRankRestriction
#print axioms exact_NativeRankSuccessorWitness
#print axioms exact_CountableNativeRanks
#print axioms compose

end LogicLineages.PersistentMarking.NativeRankChecks
