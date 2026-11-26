module
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteGlobalTail
open ActualZeroClassReplacement ActualWeightedReadNormalization ActualRankedRowColumns
open ActualReadChargeIteration ActualZeroEdgeAlphabet InnerTerminationTargets

private theorem groupedIgnoresReadValues (raw : List Read) :
    groupedWeights ((raw.map Prod.fst).map (fun t => (t,0))) = groupedWeights raw := by
  induction raw with
  | nil => rfl
  | cons rd rest ih => simp only [List.map_cons,groupedWeights,ih]

theorem exactSyntaxCharge : ExactSyntaxCharge := by
  intro r s
  simp only [syntaxCharge,syntaxOf,stateCharge,countCharge,valueCount,rankedRow,groupedIgnoresReadValues]

theorem exactGlobalLabelEnclosure : ExactGlobalLabelEnclosure := by
  intro f B ρ r zRank n initial reached path
  have seed : Covers ((syntaxOf initial).map Prod.snd) initial := by
    intro rd member
    exact List.mem_map.mpr ⟨rd.1,List.mem_map.mpr ⟨rd,member,rfl⟩,rfl⟩
  obtain ⟨budget, transport⟩ := exactTraceAlphabet f B ρ r zRank n initial reached path
  have inside : n < syntaxCharge r (syntaxOf initial) + 1 := by
    rw [exactSyntaxCharge r initial]
    omega
  intro rd member
  exact List.mem_flatMap.mpr ⟨n,List.mem_range.mpr inside,
    transport ((syntaxOf initial).map Prod.snd) seed rd member⟩

end LogicLineages.PermittedControl.ActualFiniteGlobalTail
