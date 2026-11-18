module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceCoverageProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence

theorem continuationProvenance : OrderedOccurrenceTargets.ContinuationProvenance := by
  intro xs p o hn ho
  by_cases hx : xs=[]
  · subst xs
    simp only [dispatch,↓reduceIte,List.mem_singleton] at ho
    subst o
    simp
  by_cases hi : inactive xs p=[]
  · simp only [dispatch,if_neg hx,if_pos hi,List.mem_append] at ho
    rcases ho with ht | ht
    · obtain ⟨i,hi',ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
      have hl := List.length_erase_add_one hi'
      have hs : (xs.erase i).length<xs.length := by omega
      simp [hl,hs]
    · obtain ⟨ys,hy,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨⟨a,k⟩,ha,rfl⟩ := List.mem_map.mp ht
      have hk := List.mk_mem_zipIdx_iff_getElem?.mp ha
      have hp : ys.Perm xs := List.mem_permutations.mp hy
      simp only [Nat.reduceEqDiff,false_implies,true_implies,and_true,true_and,false_or,or_true]
      exact ⟨hp,a,hk,rfl,rfl⟩
  · simp only [dispatch,if_neg hx,if_neg hi] at ho
    obtain ⟨i,hi',rfl⟩ := List.mem_map.mp ho
    simp [hi']

end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
