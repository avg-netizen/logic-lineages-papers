module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceCoverageProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence

theorem continuationProvenance : OrderedOccurrenceTargets.ContinuationProvenance := by
  intro xs p o hn ho
  by_cases hx : xs=[]
  · subst xs
    simp only [dispatch,if_pos rfl,List.mem_singleton] at ho
    subst o
    simp
  by_cases hi : inactive xs p=[]
  · simp only [dispatch,if_neg hx,if_pos hi,List.mem_append] at ho
    rcases ho with ht | ht
    · obtain ⟨i,hi',ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
      have hl := List.length_erase_add_one hi'
      simp only [Outcome.tag,Outcome.bound,Outcome.witness,Outcome.occurrence,Outcome.matrix]
      constructor
      · omega
      constructor
      · omega
      constructor
      · intro _; exact ⟨hl,by omega⟩
      constructor
      · omega
      · omega
    · obtain ⟨ys,hy,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨⟨a,k⟩,ha,rfl⟩ := List.mem_map.mp ht
      have hk := List.mk_mem_zipIdx_iff_getElem?.mp ha
      have hp : ys.Perm xs := List.mem_permutations.mp hy
      refine ⟨?_,?_,?_,?_,?_⟩
      · omega
      · omega
      · omega
      · intro _; exact ⟨hp,a,hk,rfl,rfl⟩
      · omega
  · simp only [dispatch,if_neg hx,if_neg hi] at ho
    obtain ⟨i,hi',rfl⟩ := List.mem_map.mp ho
    refine ⟨?_,?_,?_,?_,?_⟩
    · omega
    · intro _; exact ⟨rfl,hi',rfl⟩
    · omega
    · omega
    · omega
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
